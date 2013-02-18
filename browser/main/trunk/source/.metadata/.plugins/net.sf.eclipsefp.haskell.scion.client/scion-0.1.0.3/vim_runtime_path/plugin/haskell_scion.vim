if !exists('g:scion_config')
  let g:scion_config = {}
  " let g:scion_config['use_default_scion_cabal_dist_dir'] = 0
endif
" probably more commands should be moved from haskell.vim into this file so
" that the commands can be run even when not editing a haskell file.

fun! s:LoadComponentCompletion(A,L,P)
  let beforeC= a:L[:a:P-1]
  let word = matchstr(beforeC, '\zs\S*$')

  let result = []
  for item in haskellcomplete#EvalScion(1,'list-cabal-components',{'cabal-file': haskellcomplete#CabalFile()})
    if has_key(item, 'library')
      call add(result, 'library') " there can only be one
    elseif has_key(item, 'executable')
      call add(result, 'executable:'. item['executable'])
    else
      " component type File will never be returned ?
      throw "unexpected item ".string(item)
    endif
  endfor
  return result
endf

fun! s:LoadComponentScion(...)
  let result = haskellcomplete#LoadComponent(1,call('haskellcomplete#compToV', a:000))
  echo haskellcomplete#ScionResultToErrorList('load component finished: ','setqflist', result)

  " start checking file on buf write
  if !exists('g:dont_check_on_buf_write')
    augroup HaskellScion
      au BufWritePost *.hs,*.hsc,*.lhs silent! BackgroundTypecheckFile
    augroup end
  endif
endf


" arg either "library", "executable:name" or "file:Setup.hs"
" no args: file:<current file>
command! -nargs=? -complete=customlist,s:LoadComponentCompletion
  \ LoadComponentScion
  \ call s:LoadComponentScion(<f-args>)

command! -nargs=* -complete=file -buffer WriteSampleConfigScion
  \ echo haskellcomplete#WriteSampleConfig(<f-args>) | e .scion-config
