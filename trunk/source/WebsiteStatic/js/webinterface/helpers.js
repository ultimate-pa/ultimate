/**
 * Check if "key: value" exists in any tool config.
 * @param key
 * @param value
 * @returns {boolean}
 */
function tool_config_key_value_exists(key, value) {
  for (const tool_config of Object.values(_CONFIG.tools)) {
    if (key in tool_config) {
      if (tool_config[key] === value) {
        return true;
      }
    }
  }

  return false;
}


/**
 * Fetch window.location URL parameters
 * @returns {{tool: *, session: *, lang: *, sample: *}}
 */
function get_url_params() {
  let url = new URL(window.location);

  return {
    "tool": url.searchParams.get("tool"),
    "session": url.searchParams.get("session"),
    "lang": url.searchParams.get("lang"),
    "sample": url.searchParams.get("sample")
  };
}


/**
 * Returns the current workers language or "undefined" if none set.
 */
function get_current_language() {
  let result = "undefined";
  if ("current_worker" in _CONFIG.context) {
    result = _CONFIG.context.current_worker.language;
  }
  return result
}


/**
 * Compress an array into URI save string.
 * @param array_to_compress
 * @returns {string}
 */
function URICompressArray(array_to_compress) {
  return LZString.compressToEncodedURIComponent(JSON.stringify(array_to_compress));
}


/**
 * Decompress a string compressed with URICompressArray back into an array.
 * !string_to_decompress has to be retrieved with URL.searchParams or decodeURIComponent should be applied.
 * @param string_to_decompress
 */
function URIDecompressArray(string_to_decompress) {
  return JSON.parse(LZString.decompressFromEncodedURIComponent(string_to_decompress));
}

/**
 * Copy the content of an input field to the users clipboard.
 * @param input_element
 */
function copy_to_clipboard(input_element) {
  input_element.select();
  document.execCommand('copy');
}
