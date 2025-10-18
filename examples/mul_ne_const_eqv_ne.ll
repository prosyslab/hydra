define i1 @src(i8 %x) {
  %a = mul i8 %x, 5
  %b = icmp ne i8 %a, 30
  ret i1 %b
}


define i1 @tgt(i8 %x) {
  %b = icmp ne i8 %x, 6
}

