let _ =
  CmdLineParser.parse_cmdline_x64 [
    ("check_aesni",  (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_aesni_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_aesni_stdcall win), 0, true);
    ("check_sha",    (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_sha_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_sha_stdcall win), 0, true);
    ("check_adx_bmi2",  (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_adx_bmi2_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_adx_bmi2_stdcall win), 0, true);
    ("check_avx",     (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_avx_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_avx_stdcall win), 0, true);
    ("check_avx2",    (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_avx2_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_avx2_stdcall win), 0, true);
    ("check_movbe",    (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_movbe_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_movbe_stdcall win), 0, true);
    ("check_sse",    (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_sse_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_sse_stdcall win), 0, true);
    ("check_rdrand",    (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_rdrand_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_rdrand_stdcall win), 0, true);
    ("check_avx512",    (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_avx512_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_avx512_stdcall win), 0, true);
    ("check_osxsave",    (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_osxsave_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_osxsave_stdcall win), 0, true);
    ("check_avx_xcr0",    (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_avx_xcr0_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_avx_xcr0_stdcall win), 0, true);
    ("check_avx512_xcr0",    (fun win -> Vale_Lib_X64_Cpuidstdcall.va_code_Check_avx512_xcr0_stdcall win, Vale_Lib_X64_Cpuidstdcall.va_codegen_success_Check_avx512_xcr0_stdcall win), 0, true);
  ]
