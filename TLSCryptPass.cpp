#include "TLSCryptPass.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Comdat.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/User.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <cstdint>
#include <cstring>
#include <utility>

using namespace llvm;

llvm::cl::opt<bool> TLSCryptEnable("obftlscrypt", llvm::cl::init(true), llvm::cl::desc("Master Toggle"));

static constexpr unsigned CloneCap = 10;
static constexpr unsigned CloneSizeBudget = 4096;
static constexpr bool LocalOnly = true;
static constexpr bool SkipMixedCallers = true;
static constexpr bool EnablePrologue = true;
static constexpr bool EnableBodyEncryption = true;
static constexpr bool EncConsts = true;
static constexpr bool EncStrings = true;
static constexpr bool EncGVPtrs = true;
static constexpr bool IndirectCallsEnabled = true;
static constexpr bool IndirectBranchesEnabled = true;
static constexpr bool EnableCloneTier = true;
static constexpr bool AdmitPersonality = true;
static constexpr bool EnableThunkFallback = true;

static constexpr uint64_t FNV1a64(const char* s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    while (*s)
    {
        h ^= (uint8_t)(*s);
        h *= 0x100000001b3ULL;
        ++s;
    }
    return h;
}

static uint64_t FNV1a64Range(StringRef s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    for (char c : s)
    {
        h ^= (uint8_t)c;
        h *= 0x100000001b3ULL;
    }
    return h;
}

static bool IsCRTSpecial(StringRef n)
{
    if (n.starts_with("_tls_callback")) return true;
    switch (FNV1a64Range(n))
    {
        case FNV1a64("DllMain"):
        case FNV1a64("_DllMainCRTStartup"):
        case FNV1a64("DllMainCRTStartup"):
        case FNV1a64("mainCRTStartup"):
        case FNV1a64("wmainCRTStartup"):
        case FNV1a64("WinMainCRTStartup"):
        case FNV1a64("wWinMainCRTStartup"):
        case FNV1a64("_CRT_INIT"):
        case FNV1a64("__scrt_common_main"):
        case FNV1a64("__scrt_common_main_seh"):
        case FNV1a64("__scrt_dllmain_before_initialize_c"):
        case FNV1a64("__scrt_dllmain_after_initialize_c"):
            return true;
    }
    return false;
}

static bool IsCompilerHelper(StringRef n)
{
    if (n.starts_with("__GSHandlerCheck")) return true;
    if (n.starts_with("_RTC_")) return true;
    if (n.starts_with("__scrt_")) return true;
    if (n.starts_with("__acrt_")) return true;
    if (n.starts_with("__crt_")) return true;
    switch (FNV1a64Range(n))
    {
        case FNV1a64("_chkstk"):
        case FNV1a64("__chkstk"):
        case FNV1a64("__chkstk_ms"):
        case FNV1a64("__security_check_cookie"):
        case FNV1a64("__security_init_cookie"):
        case FNV1a64("__CxxFrameHandler3"):
        case FNV1a64("__CxxFrameHandler4"):
        case FNV1a64("__C_specific_handler"):
        case FNV1a64("__CxxThrowException"):
        case FNV1a64("__std_terminate"):
        case FNV1a64("__std_exception_copy"):
        case FNV1a64("__std_exception_destroy"):
        case FNV1a64("__RTDynamicCast"):
        case FNV1a64("__RTtypeid"):
        case FNV1a64("__RTCastToVoid"):
        case FNV1a64("_purecall"):
        case FNV1a64("__purecall"):
        case FNV1a64("__report_rangecheckfailure"):
        case FNV1a64("__report_securityfailure"):
        case FNV1a64("_Init_thread_header"):
        case FNV1a64("_Init_thread_footer"):
        case FNV1a64("_Init_thread_abort"):
        case FNV1a64("_Init_thread_epoch"):
        case FNV1a64("__msvc_align"):
            return true;
    }
    return false;
}

static bool IsOurHelper(StringRef n)
{
    if (n.starts_with("__tlscrypt_")) return true;
    if (n.starts_with("__retcrypt_")) return true;
    return false;
}

static bool IsMSVCHelperCallee(StringRef n)
{
    if (n.starts_with("__imp_")) return true;
    if (n.starts_with("__delayLoadHelper")) return true;
    switch (FNV1a64Range(n))
    {
        case FNV1a64("__chkstk"):
        case FNV1a64("_alloca_probe"):
        case FNV1a64("__security_check_cookie"):
        case FNV1a64("__security_init_cookie"):
        case FNV1a64("__GSHandlerCheck"):
        case FNV1a64("__GSHandlerCheck_SEH"):
        case FNV1a64("__GSHandlerCheck_EH"):
        case FNV1a64("__CxxFrameHandler3"):
        case FNV1a64("__CxxFrameHandler4"):
        case FNV1a64("__C_specific_handler"):
        case FNV1a64("_setjmp"):
        case FNV1a64("_setjmp3"):
        case FNV1a64("longjmp"):
            return true;
    }
    return false;
}

static bool IsVTableGV(StringRef n)
{
    if (n.starts_with("??_7")) return true;
    if (n.starts_with("??_R4")) return true;
    if (n.starts_with("_ZTV")) return true;
    if (n.starts_with("_ZTC")) return true;
    if (n.starts_with("_ZTT")) return true;
    return false;
}

static void CollectGlobalCtorDtorFuncs(Module& m, DenseSet<Function*>& out)
{
    const StringRef tables[] = {"llvm.global_ctors", "llvm.global_dtors"};
    for (StringRef tn : tables)
    {
        GlobalVariable* gv = m.getNamedGlobal(tn);
        if (!gv || !gv->hasInitializer()) continue;
        auto* ca = dyn_cast<ConstantArray>(gv->getInitializer());
        if (!ca) continue;
        for (unsigned i = 0; i < ca->getNumOperands(); ++i)
        {
            auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
            if (!cs || cs->getNumOperands() < 2) continue;
            Value* v = cs->getOperand(1)->stripPointerCasts();
            if (auto* f = dyn_cast<Function>(v)) out.insert(f);
        }
    }
}

static void CollectFunctionsFromConstant(Constant* c, DenseSet<Function*>& out, DenseSet<Constant*>& visited)
{
    if (!c) return;
    if (!visited.insert(c).second) return;
    if (auto* f = dyn_cast<Function>(c)) { out.insert(f); return; }
    for (unsigned i = 0, n = c->getNumOperands(); i < n; ++i)
        if (auto* sub = dyn_cast<Constant>(c->getOperand(i)))
            CollectFunctionsFromConstant(sub, out, visited);
}

static void CollectVTableFuncs(Module& m, DenseSet<Function*>& out)
{
    DenseSet<Constant*> visited;
    for (GlobalVariable& gv : m.globals())
    {
        if (!gv.hasInitializer()) continue;
        if (!IsVTableGV(gv.getName())) continue;
        CollectFunctionsFromConstant(gv.getInitializer(), out, visited);
    }
}

static bool UserLeadsOnlyToMetadataGlobals(User* u, DenseSet<User*>& visited)
{
    if (!visited.insert(u).second) return true;
    if (auto* gv = dyn_cast<GlobalVariable>(u))
    {
        StringRef n = gv->getName();
        switch (FNV1a64Range(n))
        {
            case FNV1a64("llvm.global.annotations"):
            case FNV1a64("llvm.used"):
            case FNV1a64("llvm.compiler.used"):
            case FNV1a64("llvm.metadata"):
                return true;
        }
        return false;
    }
    if (isa<Instruction>(u)) return false;
    if (u->user_empty()) return false;
    for (User* uu : u->users())
        if (!UserLeadsOnlyToMetadataGlobals(uu, visited))
            return false;
    return true;
}

static bool DetectAddressTaken(Function& f)
{
    for (User* u : f.users())
    {
        if (auto* cb = dyn_cast<CallBase>(u))
        {
            if (cb->getCalledOperand() != &f) return true;
            continue;
        }
        DenseSet<User*> visited;
        if (!UserLeadsOnlyToMetadataGlobals(u, visited)) return true;
    }
    return false;
}

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga || !ga->hasInitializer()) return false;
    auto* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs || cs->getNumOperands() < 2) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* annogv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annogv || !annogv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(annogv->getInitializer());
        if (!cds || !cds->isString()) continue;
        StringRef s = cds->getAsString();
        if (s.starts_with(tag) && s.size() == strlen(tag) + 1) return true;
    }
    return false;
}

static bool HasRetCryptAnnotation(Function& f)
{
    if (f.hasFnAttribute("retcrypt")) return true;
    return HasAnnotationTag(f, "retcrypt");
}

static bool HasNoRetCryptAnnotation(Function& f)
{
    return HasAnnotationTag(f, "noretcrypt");
}

static bool HasNoObfuscateAnnotation(Function& f)
{
    return HasAnnotationTag(f, "noobfus");
}

static bool IsInLlvmUsed(Function& f)
{
    Module* m = f.getParent();
    const char* names[] = {"llvm.used", "llvm.compiler.used"};
    for (const char* n : names)
    {
        GlobalVariable* gv = m->getNamedGlobal(n);
        if (!gv || !gv->hasInitializer()) continue;
        auto* ca = dyn_cast<ConstantArray>(gv->getInitializer());
        if (!ca) continue;
        for (unsigned i = 0, e = ca->getNumOperands(); i < e; ++i)
            if (ca->getOperand(i)->stripPointerCasts() == &f) return true;
    }
    return false;
}

static bool IsSelfRecursive(Function& f)
{
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            auto* cb = dyn_cast<CallBase>(&i);
            if (!cb) continue;
            if (cb->getCalledOperand() == &f) return true;
        }
    }
    return false;
}

static bool HasMustTailInBody(Function& f)
{
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            if (auto* ci = dyn_cast<CallInst>(&i))
                if (ci->isMustTailCall()) return true;
        }
    }
    return false;
}

static bool HasFuncletPadInBody(Function& f)
{
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            if (isa<FuncletPadInst>(&i)) return true;
            if (isa<CatchReturnInst>(&i)) return true;
            if (isa<CleanupReturnInst>(&i)) return true;
            if (isa<CatchSwitchInst>(&i)) return true;
        }
    }
    return false;
}

static unsigned CountDirectCallInstCallers(Function& f)
{
    unsigned n = 0;
    for (User* u : f.users())
    {
        if (auto* ci = dyn_cast<CallInst>(u))
            if (ci->getCalledOperand() == &f) ++n;
    }
    return n;
}

struct EligibleInfo
{
    bool eligible = false;
    unsigned directcallers = 0;
    bool addresstaken = false;
    bool haspersonality = false;
    bool hasinvokes = false;
};

static EligibleInfo ClassifyFunction(Function& f, const DenseSet<Function*>& ctordtorset)
{
    EligibleInfo info;
    if (f.isDeclaration() || f.isIntrinsic()) return info;
    StringRef name = f.getName();
    if (IsOurHelper(name)) return info;
    if (f.hasFnAttribute("tlscrypt-r6-thunk")) return info;
    if (f.hasFnAttribute(Attribute::Naked)) return info;
    if (IsCRTSpecial(name)) return info;
    if (IsCompilerHelper(name)) return info;
    if (ctordtorset.contains(&f)) return info;
    if (HasRetCryptAnnotation(f) || HasNoRetCryptAnnotation(f)) return info;
    if (HasNoObfuscateAnnotation(f)) return info;
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            if (isa<FuncletPadInst>(&i)) return info;
            if (isa<CatchReturnInst>(&i)) return info;
            if (isa<CleanupReturnInst>(&i)) return info;
            if (auto* ci = dyn_cast<CallInst>(&i))
                if (ci->isMustTailCall()) return info;
            if (isa<InvokeInst>(&i)) info.hasinvokes = true;
        }
    }
    info.addresstaken = DetectAddressTaken(f);
    info.haspersonality = f.hasPersonalityFn();
    for (User* u : f.users())
    {
        if (auto* cb = dyn_cast<CallBase>(u))
            if (cb->getCalledOperand() == &f) ++info.directcallers;
    }
    info.eligible = true;
    return info;
}

static Function* CreateThunk(Function& f, StringRef origname)
{
    Module* m = f.getParent();
    LLVMContext& c = m->getContext();
    GlobalValue::LinkageTypes origlink = f.getLinkage();
    GlobalValue::DLLStorageClassTypes origdll = f.getDLLStorageClass();
    GlobalValue::VisibilityTypes origvis = f.getVisibility();
    Comdat* origcomdat = f.getComdat();
    CallingConv::ID origcc = f.getCallingConv();
    Function* thunk = Function::Create(f.getFunctionType(), origlink, origname + ".tc_thunk_tmp", m);
    thunk->setCallingConv(origcc);
    thunk->copyAttributesFrom(&f);
    thunk->setDLLStorageClass(origdll);
    thunk->setVisibility(origvis);
    if (origcomdat) thunk->setComdat(origcomdat);
    thunk->addFnAttr("tlscrypt-r6-thunk", "true");
    thunk->addFnAttr(Attribute::NoInline);
    thunk->addFnAttr(Attribute::NoMerge);
    f.setName(origname + ".tc_impl");
    f.setLinkage(GlobalValue::PrivateLinkage);
    f.setDLLStorageClass(GlobalValue::DefaultStorageClass);
    f.setVisibility(GlobalValue::DefaultVisibility);
    f.setComdat(nullptr);
    thunk->setName(origname);
    // RAUW must happen BEFORE the thunk body is built; the body contains the one legitimate reference to impl that must survive, and RAUW only touches existing uses
    f.replaceAllUsesWith(thunk);
    BasicBlock* entry = BasicBlock::Create(c, "Entry", thunk);
    IRBuilder<> b(entry);
    SmallVector<Value*, 8> args;
    for (auto& arg : thunk->args()) args.push_back(&arg);
    CallInst* tailcall = b.CreateCall(f.getFunctionType(), &f, args);
    tailcall->setTailCallKind(CallInst::TCK_Tail);
    tailcall->setCallingConv(origcc);
    if (f.getReturnType()->isVoidTy())
        b.CreateRetVoid();
    else
        b.CreateRet(tailcall);
    return thunk;
}

static void RunThunkFallback(Module& m)
{
    DenseSet<Function*> ctordtorset;
    CollectGlobalCtorDtorFuncs(m, ctordtorset);
    SmallVector<Function*, 128> candidates;
    for (Function& f : m)
    {
        if (f.isDeclaration()) continue;
        if (f.hasFnAttribute(Attribute::Naked)) continue;
        StringRef name = f.getName();
        if (IsOurHelper(name) || IsCRTSpecial(name) || IsCompilerHelper(name)) continue;
        if (ctordtorset.contains(&f)) continue;
        if (HasRetCryptAnnotation(f) || HasNoRetCryptAnnotation(f)) continue;
        if (f.hasFnAttribute("tlscrypt-r6-thunk")) continue;
        if (f.isVarArg()) continue;
        if (f.hasPersonalityFn()) continue;
        if (HasFuncletPadInBody(f)) continue;
        if (HasMustTailInBody(f)) continue;
        if (f.hasComdat()) continue;
        bool atk = DetectAddressTaken(f);
        unsigned ncs = CountDirectCallInstCallers(f);
        if (!atk && ncs > 0) continue;
        candidates.push_back(&f);
    }
    for (Function* f : candidates)
    {
        std::string origname = f->getName().str();
        CreateThunk(*f, origname);
    }
}

static uint64_t NextKey()
{
    static uint64_t state = 0xB5B5B5B5CAFEF00DULL;
    state += 0x9E3779B97F4A7C15ULL;
    uint64_t x = state;
    x ^= x >> 30; x *= 0xBF58476D1CE4E5B9ULL;
    x ^= x >> 27; x *= 0x94D049BB133111EBULL;
    x ^= x >> 31;
    // fresh thread TLS reads zero; forcing the low bit keeps NextKey nonzero so a fresh thread entry never matches any baked K
    return x | 1;
}

static GlobalVariable* GetOrCreateTLSSlot(Module& m)
{
    const char* name = "__tlscrypt_slot";
    if (GlobalVariable* gv = m.getNamedGlobal(name)) return gv;
    LLVMContext& c = m.getContext();
    Type* i64 = Type::getInt64Ty(c);
    auto* gv = new GlobalVariable(m, i64, false, GlobalValue::InternalLinkage, ConstantInt::get(i64, 0), name, nullptr, GlobalValue::GeneralDynamicTLSModel);
    gv->setAlignment(Align(8));
    return gv;
}

static void CollectCallerKinds(Function& f, SmallVectorImpl<CallInst*>& callinsts, unsigned& invokecount, unsigned& callbrcount)
{
    invokecount = 0;
    callbrcount = 0;
    for (User* u : f.users())
    {
        auto* cb = dyn_cast<CallBase>(u);
        if (!cb) continue;
        if (cb->getCalledOperand() != &f) continue;
        if (isa<InvokeInst>(cb)) { ++invokecount; continue; }
        if (isa<CallBrInst>(cb)) { ++callbrcount; continue; }
        if (auto* ci = dyn_cast<CallInst>(cb))
            callinsts.push_back(ci);
    }
}

static void RewriteCallers(Function& f, uint64_t kf, GlobalVariable* slot, const SmallVectorImpl<CallInst*>& sites)
{
    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);
    auto* kconst = ConstantInt::get(i64, kf);
    for (CallInst* ci : sites)
    {
        IRBuilder<> b(ci);
        auto* st = b.CreateStore(kconst, slot);
        st->setAlignment(Align(8));
    }
}

static Value* EmitPrologueStash(Function& f, GlobalVariable* slot)
{
    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);
    BasicBlock* origentry = &f.getEntryBlock();
    BasicBlock* newentry = BasicBlock::Create(c, "TLSCryptStash", &f, origentry);
    IRBuilder<> b(newentry);
    // alloca is sized to 2 x i64 with 16-byte alignment on purpose; an 8 byte alloca would flip the frame size parity and misalign any `align 16` load the original IR assumed
    auto* kslot = b.CreateAlloca(i64, ConstantInt::get(i64, 2), "KSlot");
    kslot->setAlignment(Align(16));
    auto* kload = b.CreateLoad(i64, slot, "K");
    kload->setAlignment(Align(8));
    auto* stst = b.CreateStore(kload, kslot);
    stst->setAlignment(Align(8));
    // no verify compare and no int3 fail path on purpose; a verify would leak K_F as a cmp immediate; wrong-K failure instead comes from the body's garbage decrypts, which is both quieter and more RE hostile
    b.CreateBr(origentry);
    return kslot;
}

struct EncryptContext
{
    Value* k64 = nullptr;
    Value* k32 = nullptr;
    Value* k16 = nullptr;
    Value* k8 = nullptr;
    Value* keydiff = nullptr;
    uint64_t kf = 0;
    DenseSet<Instruction*> own;
};

static Value* KForWidth(const EncryptContext& c, unsigned w)
{
    switch (w)
    {
        case 8: return c.k8;
        case 16: return c.k16;
        case 32: return c.k32;
        case 64: return c.k64;
    }
    return nullptr;
}

static bool OperandSlotAcceptsNonConstant(Instruction* i, unsigned idx)
{
    if (isa<SwitchInst>(i)) return idx == 0;
    if (isa<GetElementPtrInst>(i)) return false;
    if (isa<AllocaInst>(i)) return idx == 0;
    if (isa<AtomicRMWInst>(i)) return false;
    if (isa<AtomicCmpXchgInst>(i)) return false;
    if (isa<FenceInst>(i)) return false;
    if (isa<CallBrInst>(i)) return false;
    if (isa<InvokeInst>(i)) return false;
    if (isa<PHINode>(i)) return false;
    if (isa<IntrinsicInst>(i)) return false;
    if (auto* cb = dyn_cast<CallBase>(i))
        if (idx == cb->getCalledOperandUse().getOperandNo()) return false;
    return true;
}

static void EmitEncryptContext(Function& f, Value* kslot, uint64_t kf, EncryptContext& ctx)
{
    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    Type* i16 = Type::getInt16Ty(c);
    Type* i8 = Type::getInt8Ty(c);
    BasicBlock& newentry = f.getEntryBlock();
    auto* br = cast<BranchInst>(newentry.getTerminator());
    BasicBlock* origentry = br->getSuccessor(0);
    IRBuilder<> b(&*origentry->getFirstInsertionPt());
    auto* k64 = b.CreateLoad(i64, kslot, "K64");
    k64->setAlignment(Align(8));
    auto* k32 = b.CreateTrunc(k64, i32, "K32");
    auto* k16 = b.CreateTrunc(k64, i16, "K16");
    auto* k8 = b.CreateTrunc(k64, i8, "K8");
    auto* kfconst = ConstantInt::get(i64, kf);
    auto* keydiff = b.CreateSub(kfconst, k64, "KeyDiff");
    ctx.k64 = k64;
    ctx.k32 = k32;
    ctx.k16 = k16;
    ctx.k8 = k8;
    ctx.keydiff = keydiff;
    ctx.kf = kf;
    ctx.own.insert(k64);
    if (auto* i = dyn_cast<Instruction>(k32)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(k16)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(k8)) ctx.own.insert(i);
    if (auto* i = dyn_cast<Instruction>(keydiff)) ctx.own.insert(i);
}

static void EncryptConstants(Function& f, EncryptContext& ctx)
{
    struct Repl { Instruction* ins; unsigned idx; ConstantInt* cop; };
    SmallVector<Repl, 64> work;
    for (BasicBlock& bb : f)
    {
        if (bb.hasName() && bb.getName().starts_with("TLSCrypt")) continue;
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            for (unsigned oi = 0, n = i.getNumOperands(); oi < n; ++oi)
            {
                auto* cop = dyn_cast<ConstantInt>(i.getOperand(oi));
                if (!cop) continue;
                unsigned w = cop->getBitWidth();
                if (w != 8 && w != 16 && w != 32 && w != 64) continue;
                if (!OperandSlotAcceptsNonConstant(&i, oi)) continue;
                work.push_back({&i, oi, cop});
            }
        }
    }
    for (const Repl& r : work)
    {
        unsigned w = r.cop->getBitWidth();
        Type* iw = IntegerType::get(f.getContext(), w);
        uint64_t cv = r.cop->getZExtValue();
        uint64_t kw = (w >= 64) ? ctx.kf : (ctx.kf & ((1ULL << w) - 1));
        uint64_t enc = cv ^ kw;
        if (w < 64) enc &= ((1ULL << w) - 1);
        Constant* encc = ConstantInt::get(iw, enc);
        IRBuilder<> b(r.ins);
        Value* dec = b.CreateXor(encc, KForWidth(ctx, w), "Dec");
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        r.ins->setOperand(r.idx, dec);
    }
}

static void EncryptStrings(Function& f, EncryptContext& ctx)
{
    DenseSet<GlobalVariable*> seen;
    SmallVector<GlobalVariable*, 16> entries;
    for (BasicBlock& bb : f)
    {
        if (bb.hasName() && bb.getName().starts_with("TLSCrypt")) continue;
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            for (unsigned oi = 0, oe = i.getNumOperands(); oi < oe; ++oi)
            {
                Value* op = i.getOperand(oi);
                Value* stripped = op;
                while (auto* gep = dyn_cast<GEPOperator>(stripped))
                    stripped = gep->getPointerOperand();
                auto* gv = dyn_cast<GlobalVariable>(stripped);
                if (!gv || !gv->isConstant() || !gv->hasInitializer()) continue;
                auto* arrt = dyn_cast<ArrayType>(gv->getValueType());
                if (!arrt) continue;
                Type* elemt = arrt->getElementType();
                if (!elemt->isIntegerTy(8) && !elemt->isIntegerTy(16)) continue;
                auto* init = dyn_cast<ConstantDataSequential>(gv->getInitializer());
                if (!init) continue;
                if (!seen.insert(gv).second) continue;
                entries.push_back(gv);
            }
        }
    }
    if (entries.empty()) return;
    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);
    for (GlobalVariable* gv : entries)
    {
        auto* init = cast<ConstantDataSequential>(gv->getInitializer());
        auto* arrt = cast<ArrayType>(gv->getValueType());
        unsigned ebits = arrt->getElementType()->getIntegerBitWidth();
        unsigned esize = ebits / 8;
        unsigned nelems = init->getNumElements();
        unsigned total = nelems * esize;
        unsigned padded = ((total + 7) / 8) * 8;
        unsigned nchunks = padded / 8;
        unsigned elemsperchunk = 8 / esize;
        unsigned nchunksaligned = (nchunks + 1u) & ~1u;
        IRBuilder<> be(&f.getEntryBlock(), f.getEntryBlock().begin());
        AllocaInst* slot = be.CreateAlloca(i64, ConstantInt::get(i64, nchunksaligned), "StrBuf");
        slot->setAlignment(Align(16));
        ctx.own.insert(slot);
        Instruction* insertafter = cast<Instruction>(ctx.keydiff);
        IRBuilder<> bd(insertafter->getParent(), std::next(insertafter->getIterator()));
        for (unsigned chunkidx = 0; chunkidx < nchunks; ++chunkidx)
        {
            uint64_t plain = 0;
            for (unsigned k = 0; k < elemsperchunk; ++k)
            {
                unsigned elemidx = chunkidx * elemsperchunk + k;
                if (elemidx >= nelems) break;
                uint64_t v = init->getElementAsInteger(elemidx);
                plain |= v << (k * ebits);
            }
            uint64_t mask = NextKey();
            uint64_t cipherct = plain + mask;
            Constant* cipherc = ConstantInt::get(i64, cipherct);
            Constant* maskc = ConstantInt::get(i64, mask);
            Value* effmask = bd.CreateAdd(maskc, ctx.keydiff, "StrEMask");
            Value* dec = bd.CreateSub(cipherc, effmask, "StrDec");
            Value* dst = bd.CreateGEP(i64, slot, ConstantInt::get(i64, chunkidx), "StrDst");
            Value* st = bd.CreateStore(dec, dst);
            if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
            if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
            if (auto* di = dyn_cast<Instruction>(dst)) ctx.own.insert(di);
            if (auto* di = dyn_cast<Instruction>(st)) ctx.own.insert(di);
        }
        SmallVector<Use*, 8> toreplace;
        for (Use& u : gv->uses())
        {
            auto* useri = dyn_cast<Instruction>(u.getUser());
            if (!useri) continue;
            if (useri->getFunction() != &f) continue;
            if (ctx.own.contains(useri)) continue;
            toreplace.push_back(&u);
        }
        for (Use* u : toreplace) u->set(slot);
    }
}

static bool ShouldEncryptGVOperand(GlobalVariable* gv)
{
    if (!gv) return false;
    if (gv->getName().starts_with("llvm.")) return false;
    if (gv->getName().starts_with("__retcrypt_")) return false;
    if (gv->getName().starts_with("__tlscrypt_")) return false;
    if (gv->isThreadLocal()) return false;
    if (gv->isConstant() && gv->hasInitializer())
    {
        if (auto* arrt = dyn_cast<ArrayType>(gv->getValueType()))
        {
            Type* elemt = arrt->getElementType();
            if ((elemt->isIntegerTy(8) || elemt->isIntegerTy(16)) && isa<ConstantDataSequential>(gv->getInitializer()))
                return false;
        }
    }
    return true;
}

static void EncryptGVPtrs(Function& f, EncryptContext& ctx)
{
    LLVMContext& c = f.getContext();
    Module* m = f.getParent();
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::getUnqual(c);
    DenseSet<GlobalVariable*> seen;
    SmallVector<GlobalVariable*, 16> gvs;
    for (BasicBlock& bb : f)
    {
        if (bb.hasName() && bb.getName().starts_with("TLSCrypt")) continue;
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            for (unsigned oi = 0, oe = i.getNumOperands(); oi < oe; ++oi)
            {
                auto* gv = dyn_cast<GlobalVariable>(i.getOperand(oi));
                if (!ShouldEncryptGVOperand(gv)) continue;
                if (!seen.insert(gv).second) continue;
                gvs.push_back(gv);
            }
        }
    }
    if (gvs.empty()) return;
    Instruction* insertafter = cast<Instruction>(ctx.keydiff);
    for (GlobalVariable* gv : gvs)
    {
        uint64_t mask = NextKey();
        Constant* addr = ConstantExpr::getPtrToInt(gv, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enc = ConstantExpr::getAdd(addr, maskc);
        auto* holder = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, enc, "__tlscrypt_gv_ref");
        holder->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
        IRBuilder<> b(insertafter->getParent(), std::next(insertafter->getIterator()));
        Value* loaded = b.CreateLoad(i64, holder, "GVLoad");
        Value* effmask = b.CreateAdd(maskc, ctx.keydiff, "GVEMask");
        Value* dec = b.CreateSub(loaded, effmask, "GVDec");
        Value* ptr = b.CreateIntToPtr(dec, ptrty, "GVP");
        if (auto* di = dyn_cast<Instruction>(loaded)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(ptr)) ctx.own.insert(di);
        SmallVector<Use*, 8> toreplace;
        for (Use& u : gv->uses())
        {
            auto* useri = dyn_cast<Instruction>(u.getUser());
            if (!useri) continue;
            if (useri->getFunction() != &f) continue;
            if (ctx.own.contains(useri)) continue;
            toreplace.push_back(&u);
        }
        for (Use* u : toreplace) u->set(ptr);
        insertafter = cast<Instruction>(ptr);
    }
}

static void IndirectCalls(Function& f, EncryptContext& ctx)
{
    LLVMContext& c = f.getContext();
    Module* m = f.getParent();
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::getUnqual(c);
    SmallVector<CallBase*, 32> toindirect;
    for (BasicBlock& bb : f)
    {
        if (bb.hasName() && bb.getName().starts_with("TLSCrypt")) continue;
        for (Instruction& i : bb)
        {
            if (ctx.own.contains(&i)) continue;
            auto* call = dyn_cast<CallBase>(&i);
            if (!call) continue;
            if (isa<CallBrInst>(call)) continue;
            if (call->isInlineAsm()) continue;
            if (auto* ci = dyn_cast<CallInst>(call))
                if (ci->isMustTailCall()) continue;
            Function* callee = call->getCalledFunction();
            if (!callee) continue;
            if (callee->isIntrinsic()) continue;
            if (callee->isVarArg()) continue;
            if (callee->getName().starts_with("__tlscrypt_")) continue;
            if (callee->getName().starts_with("__retcrypt_")) continue;
            if (IsMSVCHelperCallee(callee->getName())) continue;
            toindirect.push_back(call);
        }
    }
    for (CallBase* call : toindirect)
    {
        Function* callee = call->getCalledFunction();
        uint64_t mask = NextKey();
        Constant* addr = ConstantExpr::getPtrToInt(callee, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enc = ConstantExpr::getAdd(addr, maskc);
        auto* gv = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, enc, "__tlscrypt_ind_call");
        gv->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
        IRBuilder<> b(call);
        Value* loaded = b.CreateLoad(i64, gv, "CeeLoad");
        Value* effmask = b.CreateAdd(maskc, ctx.keydiff, "CeeEMask");
        Value* dec = b.CreateSub(loaded, effmask, "CeeDec");
        Value* fn = b.CreateIntToPtr(dec, ptrty, "CeeP");
        if (auto* di = dyn_cast<Instruction>(loaded)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(fn)) ctx.own.insert(di);
        call->setCalledOperand(fn);
    }
}

static void IndirectBranches(Function& f, EncryptContext& ctx)
{
    LLVMContext& c = f.getContext();
    Module* m = f.getParent();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    PointerType* ptrty = PointerType::getUnqual(c);
    SmallVector<BranchInst*, 32> toindirect;
    DenseMap<BasicBlock*, unsigned> tgtidx;
    SmallVector<BasicBlock*, 32> tgtordered;
    for (BasicBlock& bb : f)
    {
        if (bb.hasName() && bb.getName().starts_with("TLSCrypt")) continue;
        auto* br = dyn_cast<BranchInst>(bb.getTerminator());
        if (!br) continue;
        if (ctx.own.contains(br)) continue;
        bool hasehsucc = false;
        for (BasicBlock* succ : br->successors())
            if (succ && succ->isEHPad()) { hasehsucc = true; break; }
        if (hasehsucc) continue;
        toindirect.push_back(br);
        for (BasicBlock* succ : br->successors())
            if (tgtidx.insert({succ, (unsigned)tgtordered.size()}).second)
                tgtordered.push_back(succ);
    }
    if (toindirect.empty()) return;
    unsigned n = tgtordered.size();
    ArrayType* at = ArrayType::get(i64, n);
    SmallVector<Constant*, 32> addrentries(n);
    SmallVector<Constant*, 32> maskentries(n);
    for (unsigned i = 0; i < n; ++i)
    {
        uint64_t mask = NextKey();
        Constant* ba = BlockAddress::get(&f, tgtordered[i]);
        Constant* baint = ConstantExpr::getPtrToInt(ba, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        addrentries[i] = ConstantExpr::getAdd(baint, maskc);
        maskentries[i] = maskc;
    }
    auto* addrtable = new GlobalVariable(*m, at, false, GlobalValue::PrivateLinkage, ConstantArray::get(at, addrentries), "__tlscrypt_ind_br_addrtbl");
    addrtable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    auto* masktable = new GlobalVariable(*m, at, false, GlobalValue::PrivateLinkage, ConstantArray::get(at, maskentries), "__tlscrypt_ind_br_masktbl");
    masktable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    Constant* zero32 = ConstantInt::get(i32, 0);
    for (BranchInst* br : toindirect)
    {
        IRBuilder<> b(br);
        Value* idx;
        if (br->isConditional())
        {
            Constant* idxt = ConstantInt::get(i32, tgtidx[br->getSuccessor(0)]);
            Constant* idxf = ConstantInt::get(i32, tgtidx[br->getSuccessor(1)]);
            idx = b.CreateSelect(br->getCondition(), idxt, idxf, "BrIdx");
        }
        else
        {
            idx = ConstantInt::get(i32, tgtidx[br->getSuccessor(0)]);
        }
        Value* agep = b.CreateGEP(at, addrtable, {zero32, idx}, "BrAGep");
        Value* mgep = b.CreateGEP(at, masktable, {zero32, idx}, "BrMGep");
        Value* loaded = b.CreateLoad(i64, agep, "BrLoad");
        Value* mask = b.CreateLoad(i64, mgep, "BrMask");
        Value* effmask = b.CreateAdd(mask, ctx.keydiff, "BrEMask");
        Value* dec = b.CreateSub(loaded, effmask, "BrDec");
        Value* tgt = b.CreateIntToPtr(dec, ptrty, "BrP");
        if (auto* di = dyn_cast<Instruction>(idx)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(agep)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(mgep)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(loaded)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(mask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(dec)) ctx.own.insert(di);
        if (auto* di = dyn_cast<Instruction>(tgt)) ctx.own.insert(di);
        SmallVector<BasicBlock*, 2> succs;
        for (BasicBlock* sc : br->successors()) succs.push_back(sc);
        auto* ibr = IndirectBrInst::Create(tgt, succs.size(), br);
        for (BasicBlock* sc : succs) ibr->addDestination(sc);
        ibr->copyMetadata(*br);
        ctx.own.insert(ibr);
        br->eraseFromParent();
    }
}

static Value* InstallPrologueAndRewriteCallers(Function& f, uint64_t kf, GlobalVariable* slot, const SmallVectorImpl<CallInst*>& sites)
{
    RewriteCallers(f, kf, slot, sites);
    return EmitPrologueStash(f, slot);
}

static void EncryptBody(Function& f, uint64_t kf, Value* kslot)
{
    if (!EnableBodyEncryption) return;
    EncryptContext ctx;
    EmitEncryptContext(f, kslot, kf, ctx);
    if (EncConsts) EncryptConstants(f, ctx);
    if (EncStrings) EncryptStrings(f, ctx);
    if (EncGVPtrs) EncryptGVPtrs(f, ctx);
    if (IndirectCallsEnabled) IndirectCalls(f, ctx);
    if (IndirectBranchesEnabled) IndirectBranches(f, ctx);
}

struct Candidate
{
    Function* f;
    unsigned directcallers;
    bool addresstaken;
    bool haspersonality;
    bool hasinvokes;
};

struct TransformedFn
{
    Function* f;
    uint64_t kf;
    Value* kslot;
};

bool RunTLSCrypt(Module& m)
{
    if (!TLSCryptEnable) return false;
    bool mutated = false;
    if (EnableThunkFallback)
    {
        RunThunkFallback(m);
        mutated = true;
    }
    DenseSet<Function*> ctordtorset;
    CollectGlobalCtorDtorFuncs(m, ctordtorset);
    SmallVector<Candidate, 64> candidates;
    for (Function& f : m)
    {
        EligibleInfo info = ClassifyFunction(f, ctordtorset);
        if (!info.eligible) continue;
        candidates.push_back({&f, info.directcallers, info.addresstaken, info.haspersonality, info.hasinvokes});
    }
    if (!EnablePrologue) return mutated;
    GlobalVariable* slot = GetOrCreateTLSSlot(m);
    SmallVector<TransformedFn, 64> transformed;
    // Part A (TLS write + prologue stash) must finish for every admitted callee before any Part B runs anywhere; Part B's indirect call phase changes the called operand away from &callee, which would hide those sites from a subsequent users() walk on that callee
    for (Candidate& c : candidates)
    {
        if (c.directcallers == 0) continue;
        if (c.addresstaken) continue;
        if (c.haspersonality && !AdmitPersonality) continue;
        if (c.hasinvokes) continue;
        bool admit = c.f->hasLocalLinkage();
        if (!admit && !LocalOnly) admit = true;
        if (!admit) continue;
        if (c.f->hasDLLExportStorageClass()) continue;
        if (IsInLlvmUsed(*c.f)) continue;
        if (c.f->hasAvailableExternallyLinkage()) continue;
        if (c.f->hasWeakAnyLinkage()) continue;
        if (c.f->hasExternalWeakLinkage()) continue;
        SmallVector<CallInst*, 8> sites;
        unsigned invokecount = 0;
        unsigned callbrcount = 0;
        CollectCallerKinds(*c.f, sites, invokecount, callbrcount);
        if (SkipMixedCallers && (invokecount > 0 || callbrcount > 0)) continue;
        if (sites.empty()) continue;
        const bool clonetierbycount = (c.directcallers > 0 && c.directcallers < CloneCap);
        const unsigned bodyinstrs = c.f->getInstructionCount();
        bool recursive = false;
        if (EnableCloneTier && clonetierbycount) recursive = IsSelfRecursive(*c.f);
        const bool doclone = EnableCloneTier && clonetierbycount && bodyinstrs <= CloneSizeBudget && !recursive;
        if (doclone)
        {
            unsigned cloneidx = 0;
            for (CallInst* ci : sites)
            {
                ValueToValueMapTy vmap;
                Function* clone = CloneFunction(c.f, vmap);
                clone->setName(c.f->getName() + ".tc_c" + Twine(cloneidx++));
                clone->setLinkage(GlobalValue::PrivateLinkage);
                clone->setDLLStorageClass(GlobalValue::DefaultStorageClass);
                clone->setVisibility(GlobalValue::DefaultVisibility);
                clone->addFnAttr(Attribute::NoInline);
                clone->addFnAttr(Attribute::NoMerge);
                clone->addFnAttr("disable-tail-calls", "true");
                ci->setCalledFunction(clone);
                uint64_t kclone = NextKey();
                SmallVector<CallInst*, 1> onecaller;
                onecaller.push_back(ci);
                Value* kslotclone = InstallPrologueAndRewriteCallers(*clone, kclone, slot, onecaller);
                transformed.push_back({clone, kclone, kslotclone});
            }
        }
        else
        {
            uint64_t kf = NextKey();
            Value* kslot = InstallPrologueAndRewriteCallers(*c.f, kf, slot, sites);
            transformed.push_back({c.f, kf, kslot});
        }
    }
    for (TransformedFn& t : transformed)
        EncryptBody(*t.f, t.kf, t.kslot);
    if (!transformed.empty()) mutated = true;
    return mutated;
}

PreservedAnalyses TLSCryptPass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunTLSCrypt(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}