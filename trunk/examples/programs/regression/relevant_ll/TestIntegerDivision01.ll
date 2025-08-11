; #Safe
; ModuleID = 'c5/TestIntegerDivision01.c'
source_filename = "c5/TestIntegerDivision01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %divident = alloca i32, align 4
  %divRes = alloca i32, align 4
  %modRes = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  store i32 2, ptr %divRes, align 4
  store i32 6, ptr %modRes, align 4
  %0 = load i32, ptr %divRes, align 4
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %0)
  %1 = load i32, ptr %modRes, align 4
  %call1 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %1)
  %2 = load i32, ptr %divRes, align 4
  %cmp = icmp eq i32 %2, 2
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %if.then
  %3 = load i32, ptr %modRes, align 4
  %cmp2 = icmp eq i32 %3, 6
  br i1 %cmp2, label %if.then3, label %if.else4

if.then3:                                         ; preds = %if.end
  br label %if.end5

if.else4:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.2, i32 noundef 19, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end5:                                          ; preds = %if.then3
  store i32 -2, ptr %divRes, align 4
  store i32 6, ptr %modRes, align 4
  %4 = load i32, ptr %divRes, align 4
  %call6 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %4)
  %5 = load i32, ptr %modRes, align 4
  %call7 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %5)
  %6 = load i32, ptr %divRes, align 4
  %cmp8 = icmp eq i32 %6, -2
  br i1 %cmp8, label %if.then9, label %if.else10

if.then9:                                         ; preds = %if.end5
  br label %if.end11

if.else10:                                        ; preds = %if.end5
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 25, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end11:                                         ; preds = %if.then9
  %7 = load i32, ptr %modRes, align 4
  %cmp12 = icmp eq i32 %7, 6
  br i1 %cmp12, label %if.then13, label %if.else14

if.then13:                                        ; preds = %if.end11
  br label %if.end15

if.else14:                                        ; preds = %if.end11
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.2, i32 noundef 26, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end15:                                         ; preds = %if.then13
  store i32 -2, ptr %divRes, align 4
  store i32 -6, ptr %modRes, align 4
  %8 = load i32, ptr %divRes, align 4
  %call16 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %8)
  %9 = load i32, ptr %modRes, align 4
  %call17 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %9)
  %10 = load i32, ptr %divRes, align 4
  %cmp18 = icmp eq i32 %10, -2
  br i1 %cmp18, label %if.then19, label %if.else20

if.then19:                                        ; preds = %if.end15
  br label %if.end21

if.else20:                                        ; preds = %if.end15
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 32, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end21:                                         ; preds = %if.then19
  %11 = load i32, ptr %modRes, align 4
  %cmp22 = icmp eq i32 %11, -6
  br i1 %cmp22, label %if.then23, label %if.else24

if.then23:                                        ; preds = %if.end21
  br label %if.end25

if.else24:                                        ; preds = %if.end21
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.2, i32 noundef 33, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end25:                                         ; preds = %if.then23
  store i32 2, ptr %divRes, align 4
  store i32 -6, ptr %modRes, align 4
  %12 = load i32, ptr %divRes, align 4
  %call26 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %12)
  %13 = load i32, ptr %modRes, align 4
  %call27 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %13)
  %14 = load i32, ptr %divRes, align 4
  %cmp28 = icmp eq i32 %14, 2
  br i1 %cmp28, label %if.then29, label %if.else30

if.then29:                                        ; preds = %if.end25
  br label %if.end31

if.else30:                                        ; preds = %if.end25
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 39, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end31:                                         ; preds = %if.then29
  %15 = load i32, ptr %modRes, align 4
  %cmp32 = icmp eq i32 %15, -6
  br i1 %cmp32, label %if.then33, label %if.else34

if.then33:                                        ; preds = %if.end31
  br label %if.end35

if.else34:                                        ; preds = %if.end31
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.2, i32 noundef 40, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end35:                                         ; preds = %if.then33
  store i32 2, ptr %divRes, align 4
  store i32 0, ptr %modRes, align 4
  %16 = load i32, ptr %divRes, align 4
  %call36 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %16)
  %17 = load i32, ptr %modRes, align 4
  %call37 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %17)
  %18 = load i32, ptr %divRes, align 4
  %cmp38 = icmp eq i32 %18, 2
  br i1 %cmp38, label %if.then39, label %if.else40

if.then39:                                        ; preds = %if.end35
  br label %if.end41

if.else40:                                        ; preds = %if.end35
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 46, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end41:                                         ; preds = %if.then39
  %19 = load i32, ptr %modRes, align 4
  %cmp42 = icmp eq i32 %19, 0
  br i1 %cmp42, label %if.then43, label %if.else44

if.then43:                                        ; preds = %if.end41
  br label %if.end45

if.else44:                                        ; preds = %if.end41
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 47, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end45:                                         ; preds = %if.then43
  store i32 -2, ptr %divRes, align 4
  store i32 0, ptr %modRes, align 4
  %20 = load i32, ptr %divRes, align 4
  %call46 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %20)
  %21 = load i32, ptr %modRes, align 4
  %call47 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %21)
  %22 = load i32, ptr %divRes, align 4
  %cmp48 = icmp eq i32 %22, -2
  br i1 %cmp48, label %if.then49, label %if.else50

if.then49:                                        ; preds = %if.end45
  br label %if.end51

if.else50:                                        ; preds = %if.end45
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 53, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end51:                                         ; preds = %if.then49
  %23 = load i32, ptr %modRes, align 4
  %cmp52 = icmp eq i32 %23, 0
  br i1 %cmp52, label %if.then53, label %if.else54

if.then53:                                        ; preds = %if.end51
  br label %if.end55

if.else54:                                        ; preds = %if.end51
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 54, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end55:                                         ; preds = %if.then53
  store i32 -2, ptr %divRes, align 4
  store i32 0, ptr %modRes, align 4
  %24 = load i32, ptr %divRes, align 4
  %call56 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %24)
  %25 = load i32, ptr %modRes, align 4
  %call57 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %25)
  %26 = load i32, ptr %divRes, align 4
  %cmp58 = icmp eq i32 %26, -2
  br i1 %cmp58, label %if.then59, label %if.else60

if.then59:                                        ; preds = %if.end55
  br label %if.end61

if.else60:                                        ; preds = %if.end55
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 60, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end61:                                         ; preds = %if.then59
  %27 = load i32, ptr %modRes, align 4
  %cmp62 = icmp eq i32 %27, 0
  br i1 %cmp62, label %if.then63, label %if.else64

if.then63:                                        ; preds = %if.end61
  br label %if.end65

if.else64:                                        ; preds = %if.end61
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 61, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end65:                                         ; preds = %if.then63
  store i32 2, ptr %divRes, align 4
  store i32 0, ptr %modRes, align 4
  %28 = load i32, ptr %divRes, align 4
  %call66 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %28)
  %29 = load i32, ptr %modRes, align 4
  %call67 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %29)
  %30 = load i32, ptr %divRes, align 4
  %cmp68 = icmp eq i32 %30, 2
  br i1 %cmp68, label %if.then69, label %if.else70

if.then69:                                        ; preds = %if.end65
  br label %if.end71

if.else70:                                        ; preds = %if.end65
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 67, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end71:                                         ; preds = %if.then69
  %31 = load i32, ptr %modRes, align 4
  %cmp72 = icmp eq i32 %31, 0
  br i1 %cmp72, label %if.then73, label %if.else74

if.then73:                                        ; preds = %if.end71
  br label %if.end75

if.else74:                                        ; preds = %if.end71
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 68, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end75:                                         ; preds = %if.then73
  store i32 32, ptr %divident, align 4
  %32 = load i32, ptr %divident, align 4
  %div = sdiv i32 %32, 13
  store i32 %div, ptr %divRes, align 4
  %33 = load i32, ptr %divident, align 4
  %rem = srem i32 %33, 13
  store i32 %rem, ptr %modRes, align 4
  %34 = load i32, ptr %divRes, align 4
  %call76 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %34)
  %35 = load i32, ptr %modRes, align 4
  %call77 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %35)
  %36 = load i32, ptr %divRes, align 4
  %cmp78 = icmp eq i32 %36, 2
  br i1 %cmp78, label %if.then79, label %if.else80

if.then79:                                        ; preds = %if.end75
  br label %if.end81

if.else80:                                        ; preds = %if.end75
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 75, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end81:                                         ; preds = %if.then79
  %37 = load i32, ptr %modRes, align 4
  %cmp82 = icmp eq i32 %37, 6
  br i1 %cmp82, label %if.then83, label %if.else84

if.then83:                                        ; preds = %if.end81
  br label %if.end85

if.else84:                                        ; preds = %if.end81
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.2, i32 noundef 76, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end85:                                         ; preds = %if.then83
  store i32 32, ptr %divident, align 4
  %38 = load i32, ptr %divident, align 4
  %div86 = sdiv i32 %38, -13
  store i32 %div86, ptr %divRes, align 4
  %39 = load i32, ptr %divident, align 4
  %rem87 = srem i32 %39, -13
  store i32 %rem87, ptr %modRes, align 4
  %40 = load i32, ptr %divRes, align 4
  %call88 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %40)
  %41 = load i32, ptr %modRes, align 4
  %call89 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %41)
  %42 = load i32, ptr %divRes, align 4
  %cmp90 = icmp eq i32 %42, -2
  br i1 %cmp90, label %if.then91, label %if.else92

if.then91:                                        ; preds = %if.end85
  br label %if.end93

if.else92:                                        ; preds = %if.end85
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 83, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end93:                                         ; preds = %if.then91
  %43 = load i32, ptr %modRes, align 4
  %cmp94 = icmp eq i32 %43, 6
  br i1 %cmp94, label %if.then95, label %if.else96

if.then95:                                        ; preds = %if.end93
  br label %if.end97

if.else96:                                        ; preds = %if.end93
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.2, i32 noundef 84, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end97:                                         ; preds = %if.then95
  store i32 -32, ptr %divident, align 4
  %44 = load i32, ptr %divident, align 4
  %div98 = sdiv i32 %44, 13
  store i32 %div98, ptr %divRes, align 4
  %45 = load i32, ptr %divident, align 4
  %rem99 = srem i32 %45, 13
  store i32 %rem99, ptr %modRes, align 4
  %46 = load i32, ptr %divRes, align 4
  %call100 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %46)
  %47 = load i32, ptr %modRes, align 4
  %call101 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %47)
  %48 = load i32, ptr %divRes, align 4
  %cmp102 = icmp eq i32 %48, -2
  br i1 %cmp102, label %if.then103, label %if.else104

if.then103:                                       ; preds = %if.end97
  br label %if.end105

if.else104:                                       ; preds = %if.end97
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 91, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end105:                                        ; preds = %if.then103
  %49 = load i32, ptr %modRes, align 4
  %cmp106 = icmp eq i32 %49, -6
  br i1 %cmp106, label %if.then107, label %if.else108

if.then107:                                       ; preds = %if.end105
  br label %if.end109

if.else108:                                       ; preds = %if.end105
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.2, i32 noundef 92, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end109:                                        ; preds = %if.then107
  store i32 -32, ptr %divident, align 4
  %50 = load i32, ptr %divident, align 4
  %div110 = sdiv i32 %50, -13
  store i32 %div110, ptr %divRes, align 4
  %51 = load i32, ptr %divident, align 4
  %rem111 = srem i32 %51, -13
  store i32 %rem111, ptr %modRes, align 4
  %52 = load i32, ptr %divRes, align 4
  %call112 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %52)
  %53 = load i32, ptr %modRes, align 4
  %call113 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %53)
  %54 = load i32, ptr %divRes, align 4
  %cmp114 = icmp eq i32 %54, 2
  br i1 %cmp114, label %if.then115, label %if.else116

if.then115:                                       ; preds = %if.end109
  br label %if.end117

if.else116:                                       ; preds = %if.end109
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 99, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end117:                                        ; preds = %if.then115
  %55 = load i32, ptr %modRes, align 4
  %cmp118 = icmp eq i32 %55, -6
  br i1 %cmp118, label %if.then119, label %if.else120

if.then119:                                       ; preds = %if.end117
  br label %if.end121

if.else120:                                       ; preds = %if.end117
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.2, i32 noundef 100, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end121:                                        ; preds = %if.then119
  store i32 32, ptr %divident, align 4
  %56 = load i32, ptr %divident, align 4
  %div122 = sdiv i32 %56, 16
  store i32 %div122, ptr %divRes, align 4
  %57 = load i32, ptr %divident, align 4
  %rem123 = srem i32 %57, 16
  store i32 %rem123, ptr %modRes, align 4
  %58 = load i32, ptr %divRes, align 4
  %call124 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %58)
  %59 = load i32, ptr %modRes, align 4
  %call125 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %59)
  %60 = load i32, ptr %divRes, align 4
  %cmp126 = icmp eq i32 %60, 2
  br i1 %cmp126, label %if.then127, label %if.else128

if.then127:                                       ; preds = %if.end121
  br label %if.end129

if.else128:                                       ; preds = %if.end121
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 107, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end129:                                        ; preds = %if.then127
  %61 = load i32, ptr %modRes, align 4
  %cmp130 = icmp eq i32 %61, 0
  br i1 %cmp130, label %if.then131, label %if.else132

if.then131:                                       ; preds = %if.end129
  br label %if.end133

if.else132:                                       ; preds = %if.end129
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 108, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end133:                                        ; preds = %if.then131
  store i32 32, ptr %divident, align 4
  %62 = load i32, ptr %divident, align 4
  %div134 = sdiv i32 %62, -16
  store i32 %div134, ptr %divRes, align 4
  %63 = load i32, ptr %divident, align 4
  %rem135 = srem i32 %63, -16
  store i32 %rem135, ptr %modRes, align 4
  %64 = load i32, ptr %divRes, align 4
  %call136 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %64)
  %65 = load i32, ptr %modRes, align 4
  %call137 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %65)
  %66 = load i32, ptr %divRes, align 4
  %cmp138 = icmp eq i32 %66, -2
  br i1 %cmp138, label %if.then139, label %if.else140

if.then139:                                       ; preds = %if.end133
  br label %if.end141

if.else140:                                       ; preds = %if.end133
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 115, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end141:                                        ; preds = %if.then139
  %67 = load i32, ptr %modRes, align 4
  %cmp142 = icmp eq i32 %67, 0
  br i1 %cmp142, label %if.then143, label %if.else144

if.then143:                                       ; preds = %if.end141
  br label %if.end145

if.else144:                                       ; preds = %if.end141
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 116, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end145:                                        ; preds = %if.then143
  store i32 -32, ptr %divident, align 4
  %68 = load i32, ptr %divident, align 4
  %div146 = sdiv i32 %68, 16
  store i32 %div146, ptr %divRes, align 4
  %69 = load i32, ptr %divident, align 4
  %rem147 = srem i32 %69, 16
  store i32 %rem147, ptr %modRes, align 4
  %70 = load i32, ptr %divRes, align 4
  %call148 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %70)
  %71 = load i32, ptr %modRes, align 4
  %call149 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %71)
  %72 = load i32, ptr %divRes, align 4
  %cmp150 = icmp eq i32 %72, -2
  br i1 %cmp150, label %if.then151, label %if.else152

if.then151:                                       ; preds = %if.end145
  br label %if.end153

if.else152:                                       ; preds = %if.end145
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 123, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end153:                                        ; preds = %if.then151
  %73 = load i32, ptr %modRes, align 4
  %cmp154 = icmp eq i32 %73, 0
  br i1 %cmp154, label %if.then155, label %if.else156

if.then155:                                       ; preds = %if.end153
  br label %if.end157

if.else156:                                       ; preds = %if.end153
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 124, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end157:                                        ; preds = %if.then155
  store i32 -32, ptr %divident, align 4
  %74 = load i32, ptr %divident, align 4
  %div158 = sdiv i32 %74, -16
  store i32 %div158, ptr %divRes, align 4
  %75 = load i32, ptr %divident, align 4
  %rem159 = srem i32 %75, -16
  store i32 %rem159, ptr %modRes, align 4
  %76 = load i32, ptr %divRes, align 4
  %call160 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %76)
  %77 = load i32, ptr %modRes, align 4
  %call161 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %77)
  %78 = load i32, ptr %divRes, align 4
  %cmp162 = icmp eq i32 %78, 2
  br i1 %cmp162, label %if.then163, label %if.else164

if.then163:                                       ; preds = %if.end157
  br label %if.end165

if.else164:                                       ; preds = %if.end157
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 131, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end165:                                        ; preds = %if.then163
  %79 = load i32, ptr %modRes, align 4
  %cmp166 = icmp eq i32 %79, 0
  br i1 %cmp166, label %if.then167, label %if.else168

if.then167:                                       ; preds = %if.end165
  br label %if.end169

if.else168:                                       ; preds = %if.end165
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 132, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end169:                                        ; preds = %if.then167
  ret i32 0
}

declare i32 @printf(ptr noundef, ...) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}




