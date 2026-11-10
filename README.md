# Caller Const Key Pass
Built for LLVM 19.1 - Windows x64 <br> <br>

This is a component of Nessa's homomorphism engine.<br> 
The idea is very simple. You may have heard of SIMD Laundering, its a method of preserving SIMD regs to then use them to move data into a function, The issue is SIMD isn't reliable, you have no idea if they will be reserved at all call sites to launder data in. TLS on the otherhand, it will be. <br>
We search for functions that have a singular xref (All Nessa binaries strip every none library function to no xrefs unless it is high traffic), then uses an unused TLS slot to launder an encryption key into the function <br>
This means without knowing the caller's site, you can't decrypt its contents. The caller site is turned into an indirect call and is encrypted ofcourse, so call graphs will not help you. <br>

### TLS CallSite
<img width="992" height="124" alt="image" src="https://github.com/user-attachments/assets/e834dc8e-022d-4ba9-82b7-a846022337e5" />
<br>

### TLS Use
<img width="995" height="903" alt="image" src="https://github.com/user-attachments/assets/1880698c-6d8e-4f61-898e-f80188e0cb22" />

## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll
