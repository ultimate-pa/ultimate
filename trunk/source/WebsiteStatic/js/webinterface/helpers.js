/**
 * Fetch window.location URL parameters
 * @returns {{tool: *, session: *, lang: *, sample: *}}
 */
function getUrlParams() {
  let url = new URL(window.location);

  return {
    'tool': url.searchParams.get('tool'),
    'session': url.searchParams.get('session'),
    'lang': url.searchParams.get('lang'),
    'sample': url.searchParams.get('sample'),
  };
}


/**
 * Returns the current workers language or "undefined" if none set.
 */
function getCurrentLanguage() {
  let result = 'undefined';
  if ('current_worker' in _CONTEXT) {
    result = _CONTEXT.current_worker.language;
  }
  return result;
}


/**
 * Compress an array into URI save string.
 * @param arrayToCompress
 * @returns {string}
 */
function URICompressArray(arrayToCompress) {
  return LZString.compressToEncodedURIComponent(JSON.stringify(arrayToCompress));
}


/**
 * Decompress a string compressed with URICompressArray back into an array.
 * !stringToDecompress has to be retrieved with URL.searchParams or decodeURIComponent should be applied.
 * @param stringToDecompress
 */
function URIDecompressArray(stringToDecompress) {
  return JSON.parse(LZString.decompressFromEncodedURIComponent(stringToDecompress));
}

/**
 * Copy the content of an input field to the users' clipboard.
 * @param inputElement
 */
function copyToClipboard(inputElement) {
  inputElement.select();
  document.execCommand('copy');
}
