
//______________________________________________________________________________
//______________________________ MESSAGES ______________________________________
//______________________________________________________________________________

function toast(txt, html, time)
{
  txt += '';
  if (!txt || txt.length == 0) return;
  
  time = time || txt.length * 200;
  
  var toastHolderId = 'toast_holder';
  
  var toastHolder = document.getElementById(toastHolderId);
  
  if (!toastHolder) 
  {
    toastHolder = document.body.appendChild(document.createElement('div'));
    toastHolder.id = toastHolderId;
    toastHolder.style.height = '';
    toastHolder.dataset.height = toastHolder.clientHeight;
  }
  
  toastHolder.style.height = toastHolder.clientHeight + 'px';
  
  var el = document.createElement('div');
  el.style.display = 'none';
  
  var toast = toastHolder.insertBefore(el, toastHolder.firstChild);
  
  if (html)     $(toast).html(txt);
  else          $(toast).text(txt);
  
  setTimeout( function(toastHolder, toast)
              {
                toast.style.display = '';
                
                var style = toast.currentStyle || window.getComputedStyle(toast);
                var marginTop = style.marginTop;
                if (marginTop.substr(-1) == '%')
                  marginTop = document.body.clientHeight * .015 + 'px';
                
                toast.dataset.height = toast.clientHeight + parseInt(marginTop);
                var newHeight = (parseInt(toastHolder.dataset.height) + parseInt(toast.dataset.height) + (toastHolder.children.length == 1 ? parseInt(marginTop) : 0));
                
                toastHolder.dataset.height = newHeight;
                toastHolder.style.height = newHeight + 'px';
                $(toast).addClass('show');
                $(toastHolder).addClass('show');
              }, 50, toastHolder, toast);
  
  setTimeout( function(toastHolder, toast)
              {
                var newHeight = (parseInt(toastHolder.dataset.height) - parseInt(toast.dataset.height));
                
                toastHolder.dataset.height = newHeight;
                toastHolder.style.height = newHeight + 'px';
                if (toastHolder.children.length == 1)
                {
                  toastHolder.dataset.height = '0';
                  toastHolder.style.height = '0px';
                }
                
                toast.style.marginTop = '-' + toast.dataset.height + 'px';
                $(toast).removeClass('show');
                $(toastHolder).removeClass('show');
              }, Math.max(1000, time), toastHolder, toast);
  
  setTimeout( function(toastHolder, toast)
              {
                removeElement(toast);
                if (toastHolder.children.length == 0) removeElement(toastHolder);
              }, Math.max(1000, time) + 400, toastHolder, toast);
}
