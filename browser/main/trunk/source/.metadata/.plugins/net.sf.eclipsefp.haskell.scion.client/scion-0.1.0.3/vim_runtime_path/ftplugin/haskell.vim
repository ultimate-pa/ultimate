if exists('g:dont_load_haskell_scion_interface_simple')
  finish
endif

" r = scion result with error locations
" func : either setqflist or setloclist
if !exists('g:haskell_qf_hook')
  let g:haskell_qf_hook = 'call haskellcomplete#SaneHook()'
endif

" very simple user interface to expose scion functionality
" I'll implement a better interface in tovl.
" (http://github.com/MarcWeber/theonevimlib)

fun! s:BackgroundTypecheckFile(...)
  " no file given defaults to current buffer
  let file = a:0 > 0 ? a:1 : expand('%:p')
  let r = haskellcomplete#EvalScion(1, 'background-typecheck-file', {'file' : file})
  if has_key(r,'Right')
    echo haskellcomplete#ScionResultToErrorList('file check', 'setqflist', r['Right'])
  else
    call setqflist([{'text' : r['Left']}])
    cope
    " isn't shown because silent is used below.. and silent is used so that
    " <cr> need not to be pressed over and over again
    echo "this file could not be checked, reason: ".r['Left']."(-> backgroundTypecheckFile)"
  endif
endf

fun! s:FlagCompletion(A,L,P)
  let beforeC= a:L[:a:P-1]
  let word = matchstr(beforeC, '\zs\S*$')
  let list = haskellcomplete#List("supported-flags")
  "allow glob patterns: 
  call filter(list, 'v:val =~ '.string('^'.substitute(word,'*','.*','g')))
  return list
endf

fun! s:ListCabalConfigurations(...)
  let params = { 'cabal-file' : haskellcomplete#CabalFile()}
  if a:0 > 0
    let params['type'] = a:1
  endif
  return haskellcomplete#EvalScion(1,'list-cabal-configurations', params)
endf

" intentionally suffixing commands by "Scion"
" This way you have less typing. You can still get a list of Scion commands by
" :*Scion<c-d>

" ===== you don't need any project for these:  =============
command! -buffer ConnectionInfoScion
  \ echo haskellcomplete#EvalScion(1,'connection-info',{})

" list supported languages
command! -buffer ListSupportedLanguagesScion
  \ echo haskellcomplete#List('supported-languages')

" list supported pragmas
command! -buffer ListSupportedPragmasScion
  \ echo haskellcomplete#List('supported-pragmas')

command! -buffer ListSupportedFlagsScion
  \ echo haskellcomplete#List('supported-flags')

command! -buffer ListRdrNamesInScopeScion
  \ echo haskellcomplete#List('rdr-names-in-scope')

command! -buffer ListCabalComponentsScion
  \ echo haskellcomplete#EvalScion(1,'list-cabal-components',{'cabal-file': haskellcomplete#CabalFile()})

command! -buffer ListExposedModulesScion
  \ echo haskellcomplete#List('exposed-modules')

command! -nargs=* ListCabalConfigurationsScion
  \ echo s:ListCabalConfigurations(<f-args>)

command! -nargs=1 SetGHCVerbosityScion
  \ echo haskellcomplete#EvalScion(1,'set-ghc-verbosity',{'level': 1*<f-args>})

command! -nargs=1 SetVerbosityScion
  \ echo haskellcomplete#EvalScion(1,'set-verbosity',{'level': 1*<f-args>})

command! -nargs=0 GetVerbosityScion
  \ echo haskellcomplete#EvalScion(1,'get-verbosity',{})

command! -nargs=0 CurrentComponentScion
  \ echo haskellcomplete#EvalScion(1,'current-component',{})

" command! -nargs=0 CurrentCabalFileScion
"  \ echo haskellcomplete#EvalScion(1,'current-cabal-file',{})

command! -nargs=0 DumpDefinedNamesScion
  \ echo haskellcomplete#EvalScion(1,'dump-defined-names',{})

command! -nargs=0 DefinedNamesScion
  \ echo haskellcomplete#EvalScion(1,'defined-names',{})

command! -nargs=1 NameDefinitions
  \ echo haskellcomplete#EvalScion(1,'name-definitions',{'name' : <f-args>})

command! -buffer -nargs=* -complete=file BackgroundTypecheckFileScion
  \ call s:BackgroundTypecheckFile(<f-args>)

command! -nargs=0 ForceUnloadScion
  \ echo haskellcomplete#EvalScion(1,'force-unload',{})

command! -nargs=0 DumpSourcesScion
  \ echo haskellcomplete#EvalScion(1,'dump-sources',{})

command! -nargs=1 -complete=customlist,s:FlagCompletion -buffer AddCommandLineFlagScion
  \ echo haskellcomplete#EvalScion(1,'add-command-line-flag',{'flags': [<f-args>]})

" ===== loading a cabal project: ============================

" assuming pwd is current cabal directory containing the .cabal file 
" optional argument specifies the cabal build (dist) directory
command! -buffer -nargs=* -complete=file OpenCabalProjectScion
  \ echo haskellcomplete#OpenCabalProject('open-cabal-project',<f-args>)
command! -buffer -nargs=* -complete=file ConfigureCabalProjectScion
  \ echo haskellcomplete#OpenCabalProject('configure-cabal-project', <f-args>)

command! -buffer ThingAtPointScion
  \ echo haskellcomplete#EvalScion(1,'thing-at-point', {'file' : expand('%:p'), 'line' : 1*line('.'), 'column' : 1*col('.')})
