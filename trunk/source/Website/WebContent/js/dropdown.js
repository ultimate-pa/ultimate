"use strict";
/*********** ASSERT ************/
/* tool and task have children */
/*******************************/
    
window.onhashchange = function() { appendSettings(); }

function initSpinners()
{
  // inititalise _ITEMS as Item-objects
  Obj.foreach( _ITEMS, function(k,v)
  {
    new Item(k,
             _ITEMS[k].name,
             _ITEMS[k].spinnerID,
             _ITEMS[k].parentID,
             _ITEMS[k].evalText,
             _ITEMS[k].children,
             _ITEMS[k].settings,
             _ITEMS[k].preferences,
             _ITEMS[k].language,
             _ITEMS[k].taskID);
  });

  document.getElementById('play').style.display = 'none';
  
  // when DOM has items, inititalise them to _ITEMS as Item-objects
  // take all with spinnerID = 'samples' and add it to parentIDs's children
  
  /*
   * check whether #tool has one or two children
   *    -> has one: prechosen = true
   *                onclick = goto tool page
   *    -> has two: is dropdown, set onclick handler
   *                onselect: insert child
   */
  var list = document.getElementById('tool').children;
  if (list.length == 1)
  {
    // set onclick navigation
    initAsItems([list[0]]);
  }
  if (list.length == 2)
  {
    initAsItems(list[1].children);
    document.getElementById('task').style.display = 'none';
  }
  
  
  /*
   * check whether #task empty, one or two  children
   *    -> is empty: display = none;
   *    -> has one:  prechosen = true
   *                 do nothing
   *    -> has two:  prechosen = true
   *                 is dropdown, set onclick handler
   *                 onselect: insert child, set language to editor, set sample list, set settings
   * if selected: onselect (not insert child)
   *
   */
  list = document.getElementById('task').children;
  if (list.length == 0)
  {
    document.getElementById('task').style.display = 'none';
  }
  if (list.length == 2)
  {
    initAsItems(list[1].children);
  }
  
  
  /*
   * check whether #sample one or two  children
   *    -> has two:   display = none;
   *    -> has three: prechosen = true
   *                  is dropdown, set onclick handler
   *                  onselect: set sample to editor
   * if selected: onselect
   *
   */
  list = document.getElementById('samples').children;
  /*
   if (list.length == 2)
  {
    document.getElementById('samples').style.display = 'none';
  }
  */
  if (list.length == 3)
  {
    initAsItems(list[2].children);
  }
  
  // fire onselect event for #task to apply samples and settings
  if(_SPINNER.task.selected)
  {
    _SPINNER.task.selected.onselect();
    var sample = S_GET('sample');
    if(_ITEMS[sample]) _ITEMS[sample].onselect();
  }
  else
  if(_SPINNER.task.selected) _SPINNER.tool.selected.onselect();
  else
  {
    appendSettings();
    _SPINNER.samples.clear();
  }
}

function initAsItems(arr)
{
  // when DOM has items, inititalise them to _ITEMS as Item-objects
  Obj.eachElement( arr, function(k,v)
  {
    var spinnerID   = v.parentElement.parentElement.id || v.parentElement.id;
    var parentID    = null;
    var settings    = [];
    var preferences = [];
    var children    = [];
    var text        = '';
    var lang        = '';
    var tID         = null;

    var task_sel = $('#task .selected')[0];
    
    if(spinnerID == 'task')    parentID = $('#tool .selected')[0].id;
    if(spinnerID == 'samples' && task_sel) parentID = task_sel.id;
    
    if(_ITEMS[v.id])
    {
      children     = _ITEMS[v.id].children;
      settings     = _ITEMS[v.id].settings;
      preferences  = _ITEMS[v.id].preferences;
      text         = _ITEMS[v.id].evalText;
      lang         = _ITEMS[v.id].language;
      tID          = _ITEMS[v.id].taskID;
    }
    
    new Item(v.id, v.innerHTML, spinnerID, parentID, text, children, settings, preferences, lang, tID);
    v.onclick = function() { _ITEMS[v.id].onselect(); };
  });
}

function onToolSelect(self)
{
  _SPINNER.task.clear();
  _SPINNER.samples.clear();
  document.getElementById('play').style.display = 'none';
  appendSettings();
  
  // set evalText to #play
  var play = document.getElementById('play');
  var text = self.selected.evalText || play.dataset.defaultVal;
  play.firstElementChild.innerHTML = text;
  
  // auto-select task, when current language is set and available
  setTimeout(function(c){ Arr.foreach(c, function(k,v) { if(editorHasCode() && _ITEMS[v].language == _CUR_LANG) _ITEMS[v].onselect(); }); }, 50, self.selected.children);

  if(_EVENT) window.clearTimeout(_EVENT);
  _EVENT = setTimeout(alignHeaderWidth, 50);
}

function onTaskSelect(self)
{ 
  _SPINNER.samples.clear();
  document.getElementById('play').style.display = '';
  
  var lang = self.selected.language;
  
  // clear editor when content doesn't fit language
  if(lang != _CUR_LANG) _EDITOR.session.setValue(_INIT_CODE);
  
  // apply language to editor
  _CUR_LANG = lang;
  changeMode(lang);
  // apply settings
  appendSettings();

  if(_EVENT) window.clearTimeout(_EVENT);
  _EVENT = setTimeout(alignHeaderWidth, 50);
}

function onSampleSelect(self)
{
  // apply sample to editor
  selectExample(self.selected.id);
  // update url in settings
  $('#current-url').val( generateURL() );
}

function changeSetting(id, value)
{
    var setting = _SPINNER.settings.children[id];
    if(setting) setting.value = value;
    return;
}

/* type can be: DROPDOWN, INTEGER, STRING, BOOLEAN*/
function appendSettings(tool, task)
{
  tool = tool || _SPINNER.tool.selected;
  task = task || _SPINNER.task.selected;
  
  _SPINNER.settings.clear();
  $('#settings').addClass( 'button' );
  var box = document.getElementById('settings').lastElementChild;
  
  // append matching settings
  if(tool && task && task.settings && task.settings.length > 0)
  {
    _SPINNER.settings.children = [];
    Arr.foreach( task.settings, function(k,v)
    {
      var setting = _SETTINGS[v];
      box.appendChild(getElementFromSetting(setting));
      if (setting.type == 'DROPDOWN')
      {
        new Spinner(setting.id, 'hidden');
        Arr.foreach( setting.items, function(k,v) { _ITEMS[v].insert(); } );
        $('#'+setting.value.replace(/\s+/g, '')).addClass( 'selected' );
        _SPINNER[setting.id].selected = _ITEMS[setting.value];
        box.lastChild.onmouseover = function() { this.firstChild.firstChild.innerHTML = _SPINNER[this.firstChild.id].selected.name; };
        box.lastChild.onclick = box.lastChild.onmouseover;
        box.lastChild.onmouseout  = function() { this.firstChild.firstChild.innerHTML = this.dataset.label; };
      }
      _SPINNER.settings.children[setting.id] = setting;
    });
  }
  
  var el;
  
  // append general settings
  var pref = tool ? tool.preferences.fontsize : [].x; // read preference preset for current tool, can be typeof 'undefined'
  task && (pref = task.preferences.fontsize || pref); // overwrite preference preset for current task if exist
  _FONTSIZE = (typeof pref != 'undefined') ? pref : (getCookie('_FONTSIZE') || 100); // use preset fontisize and cookie otherwise
  el = document.createElement('div');
  el.appendChild(getSliderTemplate('font-size', 'Font size', _FONTSIZE, changeFontSize, '50', '150', '%'));
  box.appendChild(el);
  _COOKIE_SKIP = !!pref; // prevent writing cookie once
  el.firstChild.children[1].onchange(); // simulate onchange event, setting the cookie
  _COOKIE_SKIP = false; // stop cookie prevention
  pref && removeElement(el); // remove element if preference is preset
  
  pref = tool ? tool.preferences.orientation : [].x;
  task && (pref = task.preferences.orientation || pref);
  _AUTO_ORIENTATE = (typeof pref != 'undefined') ? false : !(getCookie('_FONTSIZE') == 'false');
  el = document.createElement('div');
  el.appendChild(getCheckTemplate('autoorientation', 'Auto orientation (layout)', setAutoOrientation, _AUTO_ORIENTATE));
  box.appendChild(el);
  _COOKIE_SKIP = !!pref;
  el.firstChild.firstChild.onchange();
  if(pref) { switchOrientation(null, pref); _COOKIE_SKIP = false; }
  pref && removeElement(el);

  pref = tool ? tool.preferences.transitions : [].x;
  task && (pref = task.preferences.transitions || pref);
  _ANIMATE = (typeof pref != 'undefined') ? !(pref == "false") : !(getCookie('_ANIMATE') == 'false');
  el = document.createElement('div');
  el.appendChild(getCheckTemplate('animations', 'Transitions', setAnimation, _ANIMATE));
  box.appendChild(el);
  _COOKIE_SKIP = !!pref;
  el.firstChild.firstChild.onchange();
  _COOKIE_SKIP = false;
  pref && removeElement(el);
  
  if(document.location.hash.indexOf('url') != -1) {
  el = document.createElement('div');
  el.appendChild(getInputTemplate('current-url', 'URL', generateURL()));
  box.appendChild(el); }
  
  box.children.length > 0 && (box.parentElement.style.display = '');
}

function getWrappedElement(el)
{
  var div = document.createElement('div');
  div.appendChild(document.createElement('div'));
  div.firstElementChild.className = 'wrapper';
  div.firstElementChild.appendChild(el);
  
  return div;
}

function getCheckTemplate(id, label, onchange, checked)
{
  /*
  <div class="wrapper check">
    <input id="*-check" type="checkbox">
    <label for="*-check"><span></span>
      Animationen
    </label>
  </div>
  */
  var div        = document.createElement('div');
  div.className  = 'wrapper check';
  div.innerHTML  = '<input id="'+id+'" type="checkbox">';
  div.innerHTML += '<label for="'+id+'"><span></span>'+label+'</label>';
  
  div.firstElementChild.onchange = onchange;
  div.firstElementChild.checked  = checked;
  
  return div;
}

function getInputTemplate(id, label, value)
{
  /*
  <div class="wrapper input">
    <label>Animationen</label>
    <input id="" type="input" value="value">
  </div>
  */
  var div        = document.createElement('div');
  div.className  = 'wrapper input';
  div.innerHTML  = '<label>'+label+'</label>';
  div.innerHTML += '<input id="'+id+'" type="text" value="'+value+'">';

  $(div.children[1]).focus(  function() { this.select(); });
  div.children[1].onchange = function() { changeSetting(this.id, this.value); };
  
  return div;
}

function getSliderTemplate(id, label, value, onchange, min, max, unit)
{
  /*
  <div class="wrapper input">
    <label>Font size</label>
    <input id="font-size" type="range" value="9" min="6" max="16" step=".5">
    <label>9pt</label>
  </div>
  */
  if(!min) min = value*0.5;
  if(!max) max = value*1.5;
  if(!unit) unit = '';
  
  // keep bullet in range
  min = Math.min(min, value*.9);
  max = Math.max(max, value*1.1);
  
  var div        = document.createElement('div');
  div.className  = 'wrapper input';
  div.innerHTML  = '<label>'+label+'</label>';
  div.innerHTML += '<input id="'+id+'" type="range" value="'+value+'" min="'+min+'" max="'+max+'" step=".05">';
  div.innerHTML += '<label>'+value+unit+'</label>';
  
  div.children[1].onchange = function(callback, unit) { return function()
      {
        this.nextSibling.innerHTML = Math.floor(this.value) + unit;
        if(callback) callback(this.value);
      }; }(onchange, unit);
      // visual feedback
    div.children[1].onmousemove = div.children[1].onchange;
    div.onmousewheel = function(e) { var el = this.children[1]; var d = e.detail ? e.detail * (-1) : e.wheelDelta; el.value = parseInt(el.value)+((d>0)?1:-1); el.onchange(); };
    
    // dynamic range extension
    div.children[1].onmouseup = function()
      {
        if(this.value-this.min < (this.max - this.min)/50) this.min = Math.floor(this.value)*0.5;
        if(this.max-this.value < (this.max - this.min)/50) this.max = Math.floor(this.value)*1.2;
        changeSetting(this.id, this.value);
      };
  
  return div;
}

function getDropdownTemplate(id, label, className)
{
  /*
  <div class="wrapper dropdown">
    <div id="" class=" button">
      <div class="label">Method</div>
      <div class="box"></div>
    </div>
  </div>
  */
  var div           = document.createElement('div');
  div.className     = 'wrapper dropdown';
  div.dataset.label = label;
  div.innerHTML     = '<div id="'+id+'" class="'+className+
                      ' button"><div class="label">'+label+
                      '</div><div class="box"></div></div>';
  
  div.firstElementChild.onclick = function()
  {
    if($(this).hasClass( 'active' )) $(this).removeClass( 'active' );
    else $(this).addClass( 'active' );
    var val = _SPINNER[this.id].selected ? _SPINNER[this.id].selected.id : '';
    changeSetting(this.id, val);
  };
  
  return div;
}

function getElementFromSetting(setting)
{
  var div;
  
  switch (setting.type)
  {
    case 'check':
    case 'BOOLEAN':
        div = getCheckTemplate(setting.id, setting.label, function() { changeSetting(this.id, this.checked); }, setting.value);
      break;
    case 'input':
    case 'STRING':
        div = getInputTemplate(setting.id, setting.label, setting.value);
      break;
    case 'INTEGER':
        div = getSliderTemplate(setting.id, setting.label, setting.value);
      break;
    case 'dropdown':
    case 'DROPDOWN':
        div = getDropdownTemplate(setting.id, setting.label, 'spinner hidden');
      break;
    case 'hidden':
        div = '';
      break;
    default:
      div = document.createElement('div');
      div.innerHTML = setting.id;
  }
  
  return div;
}

function setAnimation(e, set)
{
  _ANIMATE = set || this.checked;
  setCookie("_ANIMATE", _ANIMATE, _COOKIE_EX_DAYS);
  
  if(_ANIMATE)
    $(document.body).addClass( 'animate' );
  else
    $(document.body).removeClass( 'animate' );
}

function setAlternativeDesign()
{
  if(this.checked)
    $(document.body).addClass( 'variant' );
  else
    $(document.body).removeClass( 'variant' );
}

function setAutoOrientation()
{
  _AUTO_ORIENTATE = this.checked;
  setCookie("_AUTO_ORIENTATE", _AUTO_ORIENTATE, _COOKIE_EX_DAYS);
}

//______________________________________________________________________________
//____________________________DEFINE OBJECTS____________________________________
//______________________________________________________________________________
function Spinner(id, type)
{
  this.id       = id;
  this.type     = type;
  this.selected = null;
  
  this.register(_SPINNER);
}

Spinner.prototype = {
  
  // register to array
  register: function(arr)
    {
      arr[this.id] = this;
    },
  
  // selecting item
  onselect: function(selected, self)
    {
      self = self || this;
      
      self.selected = selected;
      
      if(self.id == 'tool' || self.id == 'task' || self.id == 'samples')
        clearResults();
      
      if(self.id == 'tool')
        onToolSelect(self);
      if(self.id == 'task')
        onTaskSelect(self);
      if(self.id == 'samples')
        onSampleSelect(self);
      
      // set choice text
      if(self.type == 'visible')
        document.getElementById(self.id).firstElementChild.innerHTML = selected.name;
    },
    
  // empty DOM, unselect and hide spinner
  clear: function()
  {
    var spinner = document.getElementById(this.id);
    
    /*if($(spinner).hasClass( 'spinner' ))*/ spinner.style.display = 'none';
    
    spinner.lastElementChild.innerHTML = '';
    spinner.firstElementChild.innerHTML = spinner.dataset.defaultVal || 'choose';
    spinner.firstElementChild.id = '';
    spinner.firstElementChild.className = 'label';
    
    $(spinner).removeClass( 'button' );
    $(spinner).removeClass( 'selection' );
    
    this.selected = null;
  },
    
  // remove selection
  deselect: function()
  {
      var spinner = document.getElementById(this.id);

      $(spinner).removeClass( 'selection' );
      $('.selected', spinner).removeClass( 'selected' );
      this.selected = null;
      
      // update url in settings
      $('#current-url').val( generateURL() );
  }
};

function Item(id, name, spinnerID, parentID, evalText, children, settings, preferences, language, taskID)
{
  this.id          = id;
  this.name        = name;
  this.spinnerID   = spinnerID;
  this.parentID    = parentID;
  this.children    = children;
  this.preferences = preferences;
  this.settings    = settings;
  this.evalText    = evalText;
  this.language    = language;
  this.taskID      = taskID;
  
  
  // add to parentID's children
  if(parentID && _ITEMS[parentID])
  {
    // this could lead to multiple similar entries
     if(!Arr.has( _ITEMS[parentID].children, id))
       _ITEMS[parentID].children.push(id);
  }
  
  // set parentID's selected
  if(spinnerID && _SPINNER[spinnerID] && $('#' + this.id).hasClass( 'selected' ))
  {
    _SPINNER[spinnerID].selected = this;
    $('#'+spinnerID).addClass( 'selection' );
  }
  
  this.register(_ITEMS);
}

Item.prototype = {

  // register spinner to array
  register: function(arr)
    {
      arr[this.id] = this;
    },
  
  // insert into DOM
  insert: function(asLabel, self)
    {
      self = self || this;
      var spinner = document.getElementById(self.spinnerID);
      
      // as single element, only insert 'label'
      if(asLabel)
      {
        spinner.firstElementChild.innerHTML = self.name;
        spinner.firstElementChild.id = self.id.replace(/\s+/g, '');
        return;
      }
      
      // else as dropdown
      var el = document.createElement('div');
      el.innerHTML = self.name;
      el.id        = self.id.replace(/\s+/g, '');
      el.onclick   = function(self) { 
          return function() { 
              self.onselect(); }; }(self);
      
      spinner.lastElementChild.appendChild(el);
    },
  
  // selecting item
  onselect: function(self)
    {
      self = self || this;
      
      var firstChild;
      
      // set as selected
      var spinner = document.getElementById(self.spinnerID);
      $('.selected', spinner).removeClass( 'selected' );
      $('#' + self.id).addClass( 'selected' );
      $(spinner).addClass( 'selection' );
      
      // propagate event to parent
      _SPINNER[self.spinnerID].onselect(self);
      
      // append children to childSpinner
      if(self.children && self.children.length > 0)
      {
        // remove previous child spinner from DOM
        firstChild = _ITEMS[self.children[0]];
        var childSpinner = _SPINNER[firstChild.spinnerID];
        var single = self.children.length == 1;
        
        if(firstChild) childSpinner.clear();
        
        // insert child spinner items
        Arr.foreach( self.children, function(k,v) { _ITEMS[v].insert(single); } );
        document.getElementById(childSpinner.id).style.display = 'block';
        if(single && childSpinner.id == 'task') { firstChild.onselect(firstChild); }
        else $('#' + childSpinner.id).addClass( 'button' );
      }
      
      alignDropdownBoxes();
      
      // close box
      $(spinner).addClass( 'disappear' );
      setTimeout(function() { $(spinner).removeClass( 'disappear active' ); }, 300);
    }
};

//______________________________________________________________________________
//_________________________INSTANTIATE OBJECTS__________________________________
//______________________________________________________________________________


new Spinner('tool', 'visible');
new Spinner('task', 'visible');
new Spinner('samples', 'hidden');
new Spinner('settings', 'hidden');
_SPINNER.settings.children = [];
    