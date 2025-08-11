; #Safe
; ModuleID = 'output_folder/TestIntegerDivision01.ll'
source_filename = "c5/TestIntegerDivision01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 2)
  %call1 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 6)
  %cmp = icmp eq i32 2, 2
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %entry
  %cmp2 = icmp eq i32 6, 6
  br i1 %cmp2, label %if.end5, label %if.else4

if.else4:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.2, i32 noundef 19, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end5:                                          ; preds = %if.end
  %call6 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef -2)
  %call7 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 6)
  %cmp8 = icmp eq i32 -2, -2
  br i1 %cmp8, label %if.end11, label %if.else10

if.else10:                                        ; preds = %if.end5
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 25, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end11:                                         ; preds = %if.end5
  %cmp12 = icmp eq i32 6, 6
  br i1 %cmp12, label %if.end15, label %if.else14

if.else14:                                        ; preds = %if.end11
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.2, i32 noundef 26, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end15:                                         ; preds = %if.end11
  %call16 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef -2)
  %call17 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef -6)
  %cmp18 = icmp eq i32 -2, -2
  br i1 %cmp18, label %if.end21, label %if.else20

if.else20:                                        ; preds = %if.end15
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 32, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end21:                                         ; preds = %if.end15
  %cmp22 = icmp eq i32 -6, -6
  br i1 %cmp22, label %if.end25, label %if.else24

if.else24:                                        ; preds = %if.end21
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.2, i32 noundef 33, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end25:                                         ; preds = %if.end21
  %call26 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 2)
  %call27 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef -6)
  %cmp28 = icmp eq i32 2, 2
  br i1 %cmp28, label %if.end31, label %if.else30

if.else30:                                        ; preds = %if.end25
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 39, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end31:                                         ; preds = %if.end25
  %cmp32 = icmp eq i32 -6, -6
  br i1 %cmp32, label %if.end35, label %if.else34

if.else34:                                        ; preds = %if.end31
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.2, i32 noundef 40, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end35:                                         ; preds = %if.end31
  %call36 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 2)
  %call37 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 0)
  %cmp38 = icmp eq i32 2, 2
  br i1 %cmp38, label %if.end41, label %if.else40

if.else40:                                        ; preds = %if.end35
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 46, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end41:                                         ; preds = %if.end35
  %cmp42 = icmp eq i32 0, 0
  br i1 %cmp42, label %if.end45, label %if.else44

if.else44:                                        ; preds = %if.end41
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 47, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end45:                                         ; preds = %if.end41
  %call46 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef -2)
  %call47 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 0)
  %cmp48 = icmp eq i32 -2, -2
  br i1 %cmp48, label %if.end51, label %if.else50

if.else50:                                        ; preds = %if.end45
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 53, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end51:                                         ; preds = %if.end45
  %cmp52 = icmp eq i32 0, 0
  br i1 %cmp52, label %if.end55, label %if.else54

if.else54:                                        ; preds = %if.end51
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 54, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end55:                                         ; preds = %if.end51
  %call56 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef -2)
  %call57 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 0)
  %cmp58 = icmp eq i32 -2, -2
  br i1 %cmp58, label %if.end61, label %if.else60

if.else60:                                        ; preds = %if.end55
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 60, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end61:                                         ; preds = %if.end55
  %cmp62 = icmp eq i32 0, 0
  br i1 %cmp62, label %if.end65, label %if.else64

if.else64:                                        ; preds = %if.end61
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 61, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end65:                                         ; preds = %if.end61
  %call66 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 2)
  %call67 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 0)
  %cmp68 = icmp eq i32 2, 2
  br i1 %cmp68, label %if.end71, label %if.else70

if.else70:                                        ; preds = %if.end65
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 67, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end71:                                         ; preds = %if.end65
  %cmp72 = icmp eq i32 0, 0
  br i1 %cmp72, label %if.end75, label %if.else74

if.else74:                                        ; preds = %if.end71
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 68, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end75:                                         ; preds = %if.end71
  %div = sdiv i32 32, 13
  %rem = srem i32 32, 13
  %call76 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %div)
  %call77 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %rem)
  %cmp78 = icmp eq i32 %div, 2
  br i1 %cmp78, label %if.end81, label %if.else80

if.else80:                                        ; preds = %if.end75
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 75, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end81:                                         ; preds = %if.end75
  %cmp82 = icmp eq i32 %rem, 6
  br i1 %cmp82, label %if.end85, label %if.else84

if.else84:                                        ; preds = %if.end81
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.2, i32 noundef 76, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end85:                                         ; preds = %if.end81
  %div86 = sdiv i32 32, -13
  %rem87 = srem i32 32, -13
  %call88 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %div86)
  %call89 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %rem87)
  %cmp90 = icmp eq i32 %div86, -2
  br i1 %cmp90, label %if.end93, label %if.else92

if.else92:                                        ; preds = %if.end85
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 83, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end93:                                         ; preds = %if.end85
  %cmp94 = icmp eq i32 %rem87, 6
  br i1 %cmp94, label %if.end97, label %if.else96

if.else96:                                        ; preds = %if.end93
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.2, i32 noundef 84, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end97:                                         ; preds = %if.end93
  %div98 = sdiv i32 -32, 13
  %rem99 = srem i32 -32, 13
  %call100 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %div98)
  %call101 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %rem99)
  %cmp102 = icmp eq i32 %div98, -2
  br i1 %cmp102, label %if.end105, label %if.else104

if.else104:                                       ; preds = %if.end97
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 91, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end105:                                        ; preds = %if.end97
  %cmp106 = icmp eq i32 %rem99, -6
  br i1 %cmp106, label %if.end109, label %if.else108

if.else108:                                       ; preds = %if.end105
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.2, i32 noundef 92, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end109:                                        ; preds = %if.end105
  %div110 = sdiv i32 -32, -13
  %rem111 = srem i32 -32, -13
  %call112 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %div110)
  %call113 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %rem111)
  %cmp114 = icmp eq i32 %div110, 2
  br i1 %cmp114, label %if.end117, label %if.else116

if.else116:                                       ; preds = %if.end109
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 99, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end117:                                        ; preds = %if.end109
  %cmp118 = icmp eq i32 %rem111, -6
  br i1 %cmp118, label %if.end121, label %if.else120

if.else120:                                       ; preds = %if.end117
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.2, i32 noundef 100, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end121:                                        ; preds = %if.end117
  %div122 = sdiv i32 32, 16
  %rem123 = srem i32 32, 16
  %call124 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %div122)
  %call125 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %rem123)
  %cmp126 = icmp eq i32 %div122, 2
  br i1 %cmp126, label %if.end129, label %if.else128

if.else128:                                       ; preds = %if.end121
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 107, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end129:                                        ; preds = %if.end121
  %cmp130 = icmp eq i32 %rem123, 0
  br i1 %cmp130, label %if.end133, label %if.else132

if.else132:                                       ; preds = %if.end129
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 108, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end133:                                        ; preds = %if.end129
  %div134 = sdiv i32 32, -16
  %rem135 = srem i32 32, -16
  %call136 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %div134)
  %call137 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %rem135)
  %cmp138 = icmp eq i32 %div134, -2
  br i1 %cmp138, label %if.end141, label %if.else140

if.else140:                                       ; preds = %if.end133
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 115, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end141:                                        ; preds = %if.end133
  %cmp142 = icmp eq i32 %rem135, 0
  br i1 %cmp142, label %if.end145, label %if.else144

if.else144:                                       ; preds = %if.end141
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 116, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end145:                                        ; preds = %if.end141
  %div146 = sdiv i32 -32, 16
  %rem147 = srem i32 -32, 16
  %call148 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %div146)
  %call149 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %rem147)
  %cmp150 = icmp eq i32 %div146, -2
  br i1 %cmp150, label %if.end153, label %if.else152

if.else152:                                       ; preds = %if.end145
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 123, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end153:                                        ; preds = %if.end145
  %cmp154 = icmp eq i32 %rem147, 0
  br i1 %cmp154, label %if.end157, label %if.else156

if.else156:                                       ; preds = %if.end153
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 124, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end157:                                        ; preds = %if.end153
  %div158 = sdiv i32 -32, -16
  %rem159 = srem i32 -32, -16
  %call160 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %div158)
  %call161 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %rem159)
  %cmp162 = icmp eq i32 %div158, 2
  br i1 %cmp162, label %if.end165, label %if.else164

if.else164:                                       ; preds = %if.end157
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 131, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end165:                                        ; preds = %if.end157
  %cmp166 = icmp eq i32 %rem159, 0
  br i1 %cmp166, label %if.end169, label %if.else168

if.else168:                                       ; preds = %if.end165
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 132, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end169:                                        ; preds = %if.end165
  ret i32 0
}

declare i32 @printf(ptr noundef, ...) #0

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}




