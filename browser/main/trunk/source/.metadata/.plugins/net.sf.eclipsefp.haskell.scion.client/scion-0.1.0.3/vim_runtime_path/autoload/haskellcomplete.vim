" This file contains the code necessary to talk to the scion server
" -> haskellcomplete#EvalScion )
"
" This implementation requires has('python') support

" You can look up some use cases in the ftplugin file.
"
" This code is based on the initial implementation found in shim by Benedikt Schmidt
" The server side code can be found in src-scion-server/Scion/Server/ProtocolVim.hs

if exists('g:tovl')
  fun! s:Log(level, msg)
    call tovl#log#Log("haskellcomplete",a:level, type(a:msg) == type("") ? a:msg : string(a:msg))
  endf
else
  fun! s:Log(level, msg)
    echoe a:msg
  endf
endif

" require python or exit
if !has('python') | call s:Log(0, "Error: scion requires vim compiled with +python") | finish | endif

let g:vim_scion_protocol_version = "0"

fun! haskellcomplete#LoadComponent(set_cabal_project, component)
  let result = haskellcomplete#EvalScion(0, 'load', { 'component' : a:component})
  if has_key(result,'error')
    if result['error']['message'] == "NoCurrentCabalProject" && a:set_cabal_project
      let cabal_project = haskellcomplete#SetCurrentCabalProject()
      return haskellcomplete#LoadComponent(0, a:component)
    else
      throw "can't handle this failure: ".string(result['error'])
    endif
  endif
  return result['result']
endf

fun! haskellcomplete#SetCurrentCabalProject()
  let configs = haskellcomplete#EvalScion(1,'list-cabal-configurations',
    \ { 'cabal-file' : haskellcomplete#CabalFile()
    \ , 'scion-default': json#IntToBool(get(g:scion_config, "use_default_scion_cabal_dist_dir", 1)) })
  let config = haskellcomplete#ChooseFromList(configs, 'select a cabal configuration')
  let result = haskellcomplete#EvalScion(1,'open-cabal-project'
              \  ,{'root-dir' : getcwd()
              \   ,'dist-dir' : config['dist-dir']
              \   ,'extra-args' : config['extra-args'] }
              \ )
endf

fun! haskellcomplete#ScionResultToErrorList(action, func, result)
  let qflist = []
  for dict in a:result['notes']
    let loc = dict['location']
    if has_key(loc, 'no-location')
      " using no-location so that we have an item to jump to.
      " ef we don't use that dummy file SaneHook won't see any errors!
      call add(qflist, { 'filename' : 'no-location'
              \ ,'lnum' : 0
              \ ,'col'  : 0
              \ ,'text' : loc['no-location']
              \ ,'type' : dict['kind'] == "error" ? "E" : "W"
              \ })
    else
      call add(qflist, { 'filename' : loc['file']
              \ ,'lnum' : loc['region'][0]
              \ ,'col'  : loc['region'][1]
              \ ,'text' : ''
              \ ,'type' : dict['kind'] == "error" ? "E" : "W"
              \ })
    endif
    for msgline in split(dict['message'],"\n")
      call add(qflist, {'text': msgline})
    endfor
  endfor
  
  call call(a:func, [qflist])
  if exists('g:haskell_qf_hook')
    exec g:haskell_qf_hook
  endif
  if (len(qflist) == 0)
    return printf(a:action." success. compilationTime: %s", string(a:result['duration']))
  else
    return printf(a:action." There are errors. compilationTime: %s", string(a:result['duration']))
  endif
endfun


" if there is item take it, if there are more than one ask user which one to
" use.. -- don't think cabal allows multiple .cabal files.. At least the user
" is notified that there are more than one .cabal files
fun! haskellcomplete#ChooseFromList(list, ...)
    let msg = a:0 > 0 ? a:1 : "choose from list"
    if empty(a:list)
      return
    elseif len(a:list) == 1
      return a:list[0]
    else
      let l = []
      let i = 1
      for line in a:list
        let line2 = type(line) != type('') ? string(line) : line
        call add(l, i.': '.line2)
        let i = i + 1
        unlet line
      endfor
      return a:list[inputlist(l)-1]
    endif
endf

fun! haskellcomplete#CabalFile()
  if !exists('g:cabal_file')
    let list = split(glob('*.cabal'),"\n")
    if empty(list)
      throw "no cabal file found"
    endif
    let g:cabal_file = getcwd().'/'.haskellcomplete#ChooseFromList(list)
  endif
  return g:cabal_file
endf

fun! haskellcomplete#List(what)
  return haskellcomplete#EvalScion(1,'list-'.a:what, {})
endf

fun! haskellcomplete#OpenCabalProject(method, ...)
  return haskellcomplete#EvalScion(1,a:method
    \  ,{'root-dir' : getcwd()
    \   ,'dist-dir' : a:1
    \   ,'extra-args' : a:000[1:] }
    \ )
endf

fun! haskellcomplete#compToV(...)
  let component = a:0 > 0 ? a:1 : 'file:'.expand('%:p')
  let m = matchstr(component, '^executable:\zs.*')
  if m != '' | return {'executable' : m} | endif
  let m = matchstr(component, '^library$')
  if m != '' | return {'library' : json#NULL()} | endif
  let m = matchstr(component, '^file:\zs.*')
  if m != '' | return {'file' : m} | endif
  throw "invalid component".component
endfun

fun! haskellcomplete#WriteSampleConfig(...)
  let file = a:0 > 0 ? a:1 : ".scion-config"
  let file = fnamemodify(file, ":p")
  return haskellcomplete#EvalScion(1, 'write-sample-config', {'file' : file})
endf

" if there are errors open quickfix and jump to first error (ignoring warning)
" if not close it
fun! haskellcomplete#SaneHook()
  let list = getqflist()
  let nr = 0
  let open = 0
  let firstError = 0
  for i in getqflist()
    let nr = nr +1
    if i['bufnr'] == 0 | continue | endif
    if i['type'] == "E" && firstError == 0
      let firstError = nr
    endif
    let open = 1
  endfor
  if open
    cope " open
    " move to first error
    if firstError > 0 | exec "crewind ".firstError | endif
  else
    " if g:scion_quickfixes_always_open is set to true (non-zero) do not close
    " quickfix window even when there are not any errors.
    if exists("g:scion_quickfixes_always_open") && g:scion_quickfixes_always_open
      call setqflist([{'text' : 'No errors'}])
    else
      cclose
    endif
  endif
endf

" use this to connect to a socket
" connection settings: see strings in connectscion

" returns string part before and after cursor
function! haskellcomplete#BcAc()
  let pos = col('.') -1
  let line = getline('.')
  return [strpart(line,0,pos), strpart(line, pos, len(line)-pos)]
endfunction

" completion functions
if !exists('g:haskellcompleteAll')
  let g:haskellcompleteAll='' " '' or '-all'  '-all' means complete from the set of all function exported by all modules found in all used packages
endif

fun! haskellcomplete#CompletModule(findstart, base)
  if a:findstart
    let [bc,ac] = haskellcomplete#BcAc()
    return len(bc)-len(matchstr(bc,'\S*$'))
  else
    let [bc,ac] = haskellcomplete#BcAc()
    let addImport = bc !~ 'import\s\+\S*$'
    let matches = haskellcomplete#EvalScion(
      \ { 'request' : 'cmdModuleCompletion'
      \ , 'camelCase' : 'True'
      \ , 'short' : a:base
      \ })
    if addImport
      call map(matches, string('import ').'.v:val')
    endif
    return matches
  endif
endf

let g:scion_request_id = 1

" name: method name
" params: params to method
" optional argument: continuation function (not yet implemented)
" returns: nothing when continuation function is given
"          reply else
function! haskellcomplete#EvalScion(fail_on_error, method, params, ...)
  if a:0 > 0
    let continuation a:0
  endif
  let g:scion_request_id = g:scion_request_id + 1
  let request = { 'method' : a:method, 'params' : a:params, 'id' : g:scion_request_id }
  " the first string converts the vim object into a string, the second
  " converts this string into a python string
  let g:scion_arg = json#Encode(request)
  py evalscionAssign(vim.eval('g:scion_arg'))
  " warnings
  for w in get(g:scion_result, 'warnings', [])
    call s:Log(1, w) | echo w
  endfor
  " errors

  if !a:fail_on_error
    return g:scion_result
  endif

  if has_key(g:scion_result,'error')
    call s:Log(0, g:scion_result['error'])
    throw "There was a scion server error :".string(g:scion_result['error'])
  else
    return g:scion_result['result']
  endif
endfunction

function! s:DefPython()
python << PYTHONEOF
import sys, tokenize, cStringIO, types, socket, string, vim, os
from subprocess import Popen, PIPE

scion_log_stdout = vim.eval('exists("g:scion_log_stdout") && g:scion_log_stdout')
scion_stdout = []

class ScionServerConnection:
  """base of a server connection. They all provide two methods: send and receive bothe sending or receiving a single line separated by \\n"""
  def send(self, line):
    self.scion_i.write("%s\n"%line)
    self.scion_i.flush()
  def receive(self):
    s = self.scion_o.readline()
    if s == "":
      raise "EOF, stderr lines: \n%s"%self.scion_err.read()
    else:
      return s[:-1]

class ScionServerConnectionStdinOut(ScionServerConnection):
  """this connection launches the server and connects to its stdin and stdout streams"""
  def __init__(self, scion_executable):
    #self.scion_o,self.scion_i,e = popen2.popen3('%s -i -f /tmp/scion-log-%s' % (scion_executable, os.getcwd().replace('/','_').replace('\\','_'))
    p = Popen([scion_executable,"-i","-f", "/tmp/scion-log-%s"%(os.getcwd().replace('/','_').replace('\\','_'))], \
            shell = False, bufsize = 1, stdin = PIPE, stdout = PIPE, stderr = PIPE)
    self.scion_o = p.stdout
    self.scion_i = p.stdin
    self.scion_err = p.stderr

  def receive(self):
    global scion_log_stdout, scion_stdout
    s = ScionServerConnection.receive(self)

    # ghc doesn't always use the ghc API to print statements.. so ignore all
    # lines not marked by "scion:" at the beginning
    # see README.markdown
    while s[:6] != "scion:":
      # throw away non "scion:" line and try again
      if scion_log_stdout:
        scion_stdout.append(s)
        scion_stdout = scion_stdout[-200:]        
      # should this be printed? It doesn't hurt much but might be useful when
      # trouble shooting..
      print "ignoring line", s
      s = ScionServerConnection.receive(self)

    return s[6:]

class ScionServerConnectionSocket(ScionServerConnection):
  """connects to the scion server by either TCP/IP or socketfile"""
  def __init__(self, connection):
    if type(connection) == type([]):
      # array [ host, port ]
      # vim.eval always returns strings!
      connection = (connection[0], string.atoi(connection[1]))
      print "connection is now %s" % connection.__str__()
      su = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    else: # must be path -> file socket
      print "else "
      su = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    su.settimeout(10)
    su.connect(connection)
    # making file to use readline()
    self.scion_o = su.makefile('rw')
    self.scion_i = self.scion_o

server_connection = None
told_user_about_missing_configuration = 0
lastScionResult = "";
def connectscion():
    # check that connection method has been defined
    global server_connection
    global told_user_about_missing_configuration
    if 0 == told_user_about_missing_configuration:
      try:
        # use connection form vim value so that python is used as lazily as possible
        scionConnectionSetting = vim.eval('g:scion_connection_setting')
        print "connecting to scion %s"%scionConnectionSetting.__str__()
      except NameError:
        vim.command("sp")
        b = vim.current.buffer
        b.append( "you haven't defined g:scion_connection_setting")
        b.append( "Do so by adding one of the following lines to your .vimrc:")
        b.append( "TCP/IP, socket, stdio")
        b.append( "let g:scion_connection_setting = ['socket', \"socket file location\"] # socket connection")
        b.append( "let g:scion_connection_setting = ['socket', ['localhost', 4005]] # host, port TCIP/IP connection")
        b.append( "let g:scion_connection_setting = ['scion', \"scion_server location\"] # stdio connection ")
        told_user_about_missing_configuration = 1

    if scionConnectionSetting[0] == "socket":
      server_connection = ScionServerConnectionSocket(scionConnectionSetting[1])
    else:
      server_connection = ScionServerConnectionStdinOut(scionConnectionSetting[1])
    # tell server than vim doesn't like true, false, null
    vim.command('call haskellcomplete#EvalScion(1, "client-identify", {"name":"vim"})')

# sends a command and returns the returned line
def evalscion(str):
    global server_connection
    try:
      server_connection.send(str)
    except:
      vim.command('echom "(re)connecting to scion"')
      connectscion()
      server_connection.send(str)
    return server_connection.receive()

# str see EvalScion
def evalscionAssign(str):
  global lastScionResult
  """assigns scion result to g:scion_result, result should either be 
    { "result" : ..., "error" : [String] }"""
  vim.command("silent! unlet g:scion_result")
  lastScionResult = evalscion(str)
  vim.command("silent! let g:scion_result = %s" % lastScionResult)
  vim.command("if !exists('g:scion_result') | let g:scion_result = {'error' : \"couldn't parse scion result.\n%s\nTry :py print lastScionResult to see full server response\" } | endif " % str[:80])

# sys.path.extend(['.','..'])
PYTHONEOF
endfunction

call s:DefPython()
" vim: set et ts=4:
