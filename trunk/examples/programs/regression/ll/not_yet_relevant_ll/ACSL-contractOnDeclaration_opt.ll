; #Safe
; ModuleID = 'output_folder/ACSL-contractOnDeclaration.ll'

define dso_local i32 @main() {
entry:
  %call = call i32 @f(i32 noundef 0)
  ret i32 0
}

declare i32 @f(i32 noundef) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}




