" vim encodes strings using ''. JSON requires ".

" dummy type which is used to encode "null"
" same could be done for true / false. But we don't use those yet
fun! json#NULL()
  return function("json#NULL")
endf
fun! json#True()
  return function("json#True")
endf
fun! json#False()
  return function("json#False")
endf
fun! json#IntToBool(i)
  return  a:i == 1 ? json#True() : json#False()
endf

fun! json#Encode(thing)
  if type(a:thing) == type("")
    return '"'.escape(a:thing,'"').'"'
  elseif type(a:thing) == type({})
    let pairs = []
    for [Key, Value] in items(a:thing)
      call add(pairs, json#Encode(Key).':'.json#Encode(Value))
      unlet Key | unlet Value
    endfor
    return "{".join(pairs, ",")."}"
  elseif type(a:thing) == type(0)
    return a:thing
  elseif type(a:thing) == type([])
    return '['.join(map(a:thing, "json#Encode(v:val)"),",").']'
    return 
  elseif string(a:thing) == string(json#NULL())
    return "null"
  elseif string(a:thing) == string(json#True())
    return "true"
  elseif string(a:thing) == string(json#False())
    return "false"
  else
    throw "unexpected new thing: ".string(a:thing)
  endif
endf

" usage example: echo json#Encode({'method': 'connection-info', 'id': 0, 'params': [3]})
