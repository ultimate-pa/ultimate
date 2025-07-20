;#Safe
define i32 @main() {
entry:
  %cmp = icmp sle i32 4, 1337
  %tobool = icmp ne i32 7, 0    
  %cmpugt = icmp ugt i32 6, 2    
  %cmpuge = icmp uge i32 6, 2
  %cmpult = icmp ult i32 6, 2  
  %cmpule = icmp ule i32 6, 2 
  %cmpsgt = icmp sgt i32 6, 2    
  %cmpsge = icmp sge i32 6, 2
  %cmpslt = icmp slt i32 6, 2  
  %cmpsle = icmp sle i32 6, 2            
  ret i32 0
}

