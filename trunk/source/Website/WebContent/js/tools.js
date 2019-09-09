"use strict";

var _ANIMSec = 800;

function loading(id, loading)
{
  if(loading) $('#'+id).addClass( 'loading' );
  else        $('#'+id).removeClass( 'loading' );
}

function showNextInfo(show_again)
{
    _ANIMSec = $(document.body).hasClass( 'animate' ) ? 800 : 10;
    
    var old = $('#info-label')[0].innerHTML;
    if(!show_again) setCookie(CryptoJS.MD5(old), 1, _COOKIE_EX_DAYS);
    $('#info-label')[0].innerHTML = '';
    
    $('#header').removeClass( 'info' );
    
    if(_INFO.length > 0)
    {
      var msg = _INFO.pop();
      if(!msg || msg.length == 0) { showNextInfo(); return; }
      
      if(getCookie(CryptoJS.MD5(msg))) { showNextInfo(); return; }
      
      setTimeout(setInfoText, _ANIMSec, msg);
    }
    else
    {
      fitHeight(74);
    }
}

function setInfoText(msg)
{
  if(!msg || msg.length == 0) { showNextInfo(); return; }
    
  $('#info-label')[0].innerHTML = msg;
  $('#header').addClass( 'info' );
  setTimeout(fitHeight, _ANIMSec);
}

function fitHeight(h)
{

  if ($('#header').hasClass( 'fixed' ))
  {
    alignContentHeight(h);
    setTimeout(alignContentHeight, _ANIMSec);
  }
  if ($(document.body).hasClass( 'int' ))
  {
    alignDropdownBoxes();
    setTimeout(alignDropdownBoxes, _ANIMSec);
  }
}

function getInInterval(min, val, max)
{
    return Math.max(min, Math.min(max, val));
}

function clearSampleAndResults()
{
  // do not clear on non-visible chars
  if(!_EVENT) return;
  
  // clear ultimate results
  clearResults();
  
  // deselect sample
  _SPINNER.samples.deselect();
}

function clearResults()
{
  // signalling changes in editor
  if(_EVENT) clearTimeout(_EVENT);
  _EVENT = setTimeout( function(){ _EVENT = null; }, 500 );
  if(_CLEAR) return; _CLEAR = true;
  
  // remove all #messages.children except first
  // addClass: hide

  var msgs = $('#messages-wrapper')[0];
  while(msgs.children.length > 1) msgs.removeChild(msgs.lastChild);
  
  if(_ANIMATE && !$('#content').hasClass( 'no-messages' ))
  {
    $('#content')[0].className = 'hide';
    setTimeout( function() { $('#content')[0].className = 'no-messages'; }, 500);
  }
  else $('#content')[0].className = 'no-messages';
  
  // remove annotations
  _EDITOR.getSession().clearAnnotations();
  alignDropdownBoxes();
  setTimeout(alignDropdownBoxes, 500);
}

function checkResultsEmpty()
{
  _CLEAR = false;
  if($('#messages-wrapper')[0].children.length == 1) clearResults();
}

function removeAnnotation(i)
{
  var annot = [];
  Arr.foreach(_EDITOR.session.getAnnotations(), function(k,v) { if(k!=i) annot.push(v); });
  
  _EDITOR.session.setAnnotations(annot);
}

function editorHasCode(code)
{
    code = code || $.trim(_EDITOR.getSession().getValue());
    return !(code == '' || code == _INIT_CODE);
}

function addResults(arr, now)
{
    if(!now) { setTimeout(addResults, _ANIMATE*500, arr, true); return; }
    
    // remove .no-messages from #content
    // remove .hide        from #content
    _CLEAR = false;
    
    var annot = [];
    var wrapper = $('#content');
    if(arr.length > 0)
    {
        if(_ANIMATE && wrapper.hasClass( 'no-messages' ))
        {
          $(document.body).removeClass( 'animate' );
          wrapper[0].className = 'hide';
          setTimeout( function()
                      {
                        $(document.body).addClass( 'animate' );
                        $('#content')[0].className = '';
                      }, 10);
        }
        else wrapper[0].className = '';
    }
    else
    {
        wrapper[0].className = 'no-messages';
        toast('No Ultimate results...');
    }
    
    Arr.foreach(arr, function(k,v) { annot.push(addResult(v)); }); 

    _EDITOR.getSession().setAnnotations(annot);
    
    $('.messages-item .close').each(  function() { this.onclick = removeResult; });
    
    alignDropdownBoxes();
    setTimeout(alignDropdownBoxes, 500); 
}

function removeResult(e)
{
    e = e || window.event;
    var el = this.parentElement;
    
    var i = [].indexOf.call(el.parentNode.children, el) - 1;
    removeAnnotation(i);
    removeElement(el);
    checkResultsEmpty();
    
    e.preventDefault();
}

function addResult(res)
{
  /*
   * res: {
            endCol: -1,
            endLNr: 16,
            logLvl: "error",
            longDesc: "Variable is neither declared globally nor locally! ID=lock",
            shortDesc: "Incorrect Syntax",
            startCol: -1,
            startLNr: 16
           }
   * 
   */
    
  // append element to #messages
  var el = document.getElementById('messages-wrapper').appendChild(getResultTemplate(res));

  return {
      row: res.startLNr-1,
      column: res.startCol,
      text: res.shortDesc,
      type: res.logLvl, // also warning and information
      onclick: el.onclick
    };
}

function getSerializedSettings()
{
    // get serialized settings
    var serializedSettings = '';
    for(var i in _SPINNER.settings.children)
    {
      if(i == 'length') continue;
      // TODO: prefix is ugly, try to remove it
      // serializedSettings += '&'+i+'='+encodeURIComponent(_SPINNER.settings.children[i].value);
      serializedSettings += '&'+_SPINNER.settings.children[i].prefix+i+'='+encodeURIComponent(_SPINNER.settings.children[i].value);
    }
    return serializedSettings;
}

function serialize(box)
{
  /*
    input[text]:   name=value
    input[check]:  name=value
    input[hidden]: name=value
    select: 	   name=selected.value
  */
  /*
    input[text]:   id=value
    input[check]:  id=checked
    input[hidden]: name=value
    select: 	   id=selected.id
    (label:         id=text)
  */
  
  // return string like "name=value&id=true"
	    
}

function getResultTemplate(res)
{
    /*
     
        <div class="messages-item font-average line-top">
          <div class="msg-icon error"></div>
          <div class="msg-line">18 - 21</div>
          <div class="msg-column">34</div>
          <div class="msg-description">
            <div class="font-bold">Incorrect Syntax</div>
            <div class="msg-text">Beschreibung hier und dort</div>
          </div>
          <div class="close mini-button"></div>
        </div>
     
     */
    /*
     * res: {
              endCol: -1,
              endLNr: 16,
              logLvl: "error",
              longDesc: "Variable is neither declared globally nor locally! ID=lock",
              shortDesc: "Incorrect Syntax",
              startCol: -1,
              startLNr: 16
             }
     * 
     */

  var scopeLn  = '-';
  var scopeCol = '-';
    
  if(res.startLNr != -1 && res.endLNr != -1)
  {
      if(res.startLNr == res.endLNr) scopeLn = res.startLNr;
      else                           scopeLn = res.startLNr + ' - ' + res.endLNr;

      if(res.startCol + res.endCol == -2) {}
      else if(res.startCol == res.endCol) { scopeCol = res.startCol; }
      else if(res.startCol == -1) { res.startCol = 0; scopeCol = '0 - ' + res.endCol; }
      else if(res.endCol   == -1) { res.endCol = 0; res.endLNr++; scopeCol = res.startCol; }
      else scopeCol = res.startCol + ' - ' + res.endCol;
      if(res.startCol == 1) res.startCol--;
  }
  else if(res.startLNr != -1) scopeLn = res.startLNr + ' - ' + _EDITOR.session.getLength();
  else if(res.endLNr   != -1) scopeLn = '0 - ' + res.endLNr;
    
  var msg = document.createElement('div');
  msg.className = 'messages-item font-average line-top';
  
      var el = document.createElement('div');
      el.className = 'msg-icon ' + res.logLvl;
      msg.appendChild(el);

      el = document.createElement('div');
      el.className = 'msg-line';
      el.innerHTML = scopeLn;
      msg.appendChild(el);

      el = document.createElement('div');
      el.className = 'msg-column';
      el.innerHTML = scopeCol;
      msg.appendChild(el);

      el = document.createElement('div');
      el.className = 'msg-description';

        var div = document.createElement('div');
        div.className = 'font-bold';
        div.innerHTML = res.shortDesc;
        el.appendChild(div);
        
        div = document.createElement('div');
        div.className = 'msg-text';
        div.innerHTML = res.longDesc;
        el.appendChild(div);
        
      msg.appendChild(el);

      el = document.createElement('div');
      el.className = 'close mini-button';
      msg.appendChild(el);
      
  msg.onclick = function(r) { return function() { highlightCode(r, r.logLvl); _EDITOR.focus(); }; }(res);
      
  return msg;
}

function highlightCodeByAnnotation(e)
{
    var target = e.domEvent.target; 
    if (target.className.indexOf('ace_gutter-cell') == -1) return; 
    if (!_EDITOR.isFocused()) return; 
    if (e.clientX > 25 + target.getBoundingClientRect().left) return; 
    
    var row = e.getDocumentPosition().row;
    Arr.foreach(_EDITOR.session.getAnnotations(), function(k,v) { if(v.row == row) v.onclick(); });
}

function highlightCode(r, c)
{
  c = c || '';
    
  var startLn  = r.startLNr - 1;
  var endLn    = r.endLNr   - 1;
  var startCol = Math.max(r.startCol, 0);
  var endCol   = Math.max(r.endCol,   0);
  
  // when ednline not defined, but startline is, marker goes all the way down
  if(endLn < 0 && startLn >= 0) r.endLNr = _EDITOR.session.getLength();
  // when colums not defined, marker width = 100%
  if(r.startCol + r.endCol == -2) { endLn++;} else
  // one line selection, when columns are identical
  if(startLn == endLn && startCol == endCol) { startCol = 0; endCol = 0; endLn++; };

  if(_LAST_MARKER) _EDITOR.session.removeMarker(_LAST_MARKER);
  _LAST_MARKER = _EDITOR.session.addMarker(new Range(startLn, startCol, endLn, endCol), 'ultimate-marker '+c, 'line', true);
  setTimeout( function(marker) { if(marker) _EDITOR.session.removeMarker(marker); }, 2000, _LAST_MARKER);
  
  
  var outOfSight = !_EDITOR.isRowFullyVisible(startLn);
  _EDITOR.setAnimatedScroll(outOfSight);
  if(outOfSight) _EDITOR.scrollToLine(startLn, true, true);
  _EDITOR.navigateTo(startLn, r.startCol > 0 ? r.startCol : 0);
}

function generateURL()
{
  var url = window.location.protocol + '//' + window.location.host + window.location.pathname + '?ui=int';
  if(_SPINNER.tool.selected)    url += '&tool=' + escape(_SPINNER.tool.selected.id);
  else return url;
  if(_SPINNER.task.selected)    url += '&task=' + escape(_SPINNER.task.selected.id);
  else return url;
  if(_SPINNER.samples.selected) url += '&sample=' + escape(_SPINNER.samples.selected.id);
  return url;
}

function removeElement(el)
{
  el.parentElement.removeChild(el);
}

function isHidden(el)
{
  return (el.offsetParent === null);
}

function wait(ms)
{
    var start = new Date().getTime();
    for (var i = 0; i < 1e7; i++)
    {
      if ((new Date().getTime() - start) > ms) break;
    }
}

function S_GET(id)
{
  var a = new RegExp(id+"=([^&#=]*)");
  try { return decodeURIComponent(a.exec(window.location.search)[1]); }
  catch (e) { return null; }
}

//______________________________________________________________________________
//________________________________ LOOPING _____________________________________
//______________________________________________________________________________
/*
Array.prototype.foreach = function( callback ) {
  for( var k=0; k<this .length; k++ ) {
    if(k != 'length') {
      callback( k, this[ k ]);
    }
  }
};

Array.prototype.has = function( id ) {
  for( var k=0; k<this .length; k++ ) {
    if(k != 'length') {
      if(id == this[ k ]) return true;
    }
  }
  return false;
};

Object.prototype.foreach = function( callback ) {
  for( var k in this ) {
    if(this.hasOwnProperty(k) && k != 'length') {
     callback( k, this[ k ] );
    }
  }
};

Object.prototype.eachElement = function( callback ) {
  if (!this.length ||this.length == 0) return;
  for( var k = this.length; k > 0; k-- ) {
    callback( k-1, this[ k-1 ] );
  }
};
*/
var Arr = {};
var Obj = {};
Arr.foreach = function(arr, callback) {
    for( var k=0; k<arr.length; k++ ) {
        if(k != 'length') {
          callback( k, arr[ k ]);
        }
      }
    };

Arr.has = function(arr, id) {
    for( var k=0; k<arr.length; k++ ) {
        if(k != 'length') {
          if(id == arr[ k ]) return true;
        }
      }
      return false;
    };

Obj.foreach = function(obj, callback) {
    for( var k in obj ) {
        if(obj.hasOwnProperty(k) && k != 'length') {
         callback( k, obj[ k ] );
        }
      }
    };

Obj.eachElement = function(obj, callback) {
    if (!obj.length ||obj.length == 0) return;
    for( var k = obj.length; k > 0; k-- ) {
      callback( k-1, obj[ k-1 ] );
    }
  };
        
//__________________________________________________________________________________________________
//______________________________________ COOKIES ___________________________________________________
//__________________________________________________________________________________________________

function setCookie(c_name,value,exdays)
{
  if(_COOKIE_SKIP) { _COOKIE_SKIP = false; return; }
  
  var exdate=new Date();
  exdate.setDate(exdate.getDate() + exdays);
  var c_value=escape(value) + ((exdays==null) ? "" : "; expires="+exdate.toUTCString());
  document.cookie=c_name + "=" + c_value;
}

function getCookie(c_name)
{
  var i,x,y,ARRcookies=document.cookie.split(";");
  for (i=0;i<ARRcookies.length;i++)
  {
    x=ARRcookies[i].substr(0,ARRcookies[i].indexOf("="));
    y=ARRcookies[i].substr(ARRcookies[i].indexOf("=")+1);
    x=x.replace(/^\s+|\s+$/g,"");
    if (x==c_name) return unescape(y);
  }
  return false;
}
