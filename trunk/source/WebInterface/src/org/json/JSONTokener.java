package org.json;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StringReader;
import java.io.UnsupportedEncodingException;
import java.nio.charset.StandardCharsets;

/*
 Copyright (c) 2002 JSON.org

 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated documentation files (the "Software"), to deal
 in the Software without restriction, including without limitation the rights
 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all
 copies or substantial portions of the Software.

 The Software shall be used for Good, not Evil.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 SOFTWARE.
 */

/**
 * A JSONTokener takes a source string and extracts characters and tokens from it. It is used by the JSONObject and
 * JSONArray constructors to parse JSON source strings.
 *
 * @author JSON.org
 * @version 2011-11-24
 */
public class JSONTokener {
	/**
	 * current character.
	 */
	private int character;
	/**
	 * Whether end of file is reached.
	 */
	private boolean eof;
	/**
	 * Current index.
	 */
	private int index;
	/**
	 * Current line number.
	 */
	private int line;
	/**
	 * Previous character.
	 */
	private char previous;
	/**
	 * The reader to use.
	 */
	private final Reader reader;
	/**
	 * Whether to use the previous.
	 */
	private boolean usePrevious;

	/**
	 * Construct a JSONTokener from a Reader.
	 *
	 * @param reader
	 *            A reader.
	 */
	public JSONTokener(final Reader reader) {
		this.reader = reader.markSupported() ? reader : new BufferedReader(reader);
		eof = false;
		usePrevious = false;
		previous = 0;
		index = 0;
		character = 1;
		line = 1;
	}

	/**
	 * Construct a JSONTokener from an InputStream.
	 *
	 * @param inputStream
	 *            the input stream
	 * @throws JSONException
	 *             care for it ...
	 * @throws UnsupportedEncodingException
	 */
	public JSONTokener(final InputStream inputStream) throws UnsupportedEncodingException {
		this(new InputStreamReader(inputStream, StandardCharsets.UTF_8));
	}

	/**
	 * Construct a JSONTokener from a string.
	 *
	 * @param s
	 *            A source string.
	 */
	public JSONTokener(final String s) {
		this(new StringReader(s));
	}

	/**
	 * Back up one character. This provides a sort of lookahead capability, so that you can test for a digit or letter
	 * before attempting to parse the next number or identifier.
	 *
	 * @throws JSONException
	 *             care for it ...
	 */
	public void back() throws JSONException {
		if (usePrevious || index <= 0) {
			throw new JSONException("Stepping back two steps is not supported");
		}
		index -= 1;
		character -= 1;
		usePrevious = true;
		eof = false;
	}

	/**
	 * Get the hex value of a character (base16).
	 *
	 * @param c
	 *            A character between '0' and '9' or between 'A' and 'F' or between 'a' and 'f'.
	 * @return An int between 0 and 15, or -1 if c was not a hex digit.
	 */
	public static int dehexchar(final char c) {
		if (c >= '0' && c <= '9') {
			return c - '0';
		}
		if (c >= 'A' && c <= 'F') {
			return c - ('A' - 10);
		}
		if (c >= 'a' && c <= 'f') {
			return c - ('a' - 10);
		}
		return -1;
	}

	/**
	 * Whether the end of stream is reached.
	 *
	 * @return true if end of file and not use previous.
	 */
	public boolean end() {
		return eof && !usePrevious;
	}

	/**
	 * Determine if the source string still contains characters that next() can consume.
	 *
	 * @return true if not yet at the end of the source.
	 * @throws JSONException
	 *             care for it ...
	 */
	public boolean more() throws JSONException {
		this.next();
		if (end()) {
			return false;
		}
		back();
		return true;
	}

	/**
	 * Get the next character in the source string.
	 *
	 * @return The next character, or 0 if past the end of the source string.
	 * @throws JSONException
	 *             care for it ...
	 */
	public char next() throws JSONException {
		int c;
		if (usePrevious) {
			usePrevious = false;
			c = previous;
		} else {
			try {
				c = reader.read();
			} catch (final IOException exception) {
				throw new JSONException(exception);
			}

			if (c <= 0) { // End of stream
				eof = true;
				c = 0;
			}
		}
		index += 1;
		if (previous == '\r') {
			line += 1;
			character = c == '\n' ? 0 : 1;
		} else if (c == '\n') {
			line += 1;
			character = 0;
		} else {
			character += 1;
		}
		previous = (char) c;
		return previous;
	}

	/**
	 * Consume the next character, and check that it matches a specified character.
	 *
	 * @param c
	 *            The character to match.
	 * @return The character.
	 * @throws JSONException
	 *             if the character does not match.
	 */
	public char next(final char c) throws JSONException {
		final char n = this.next();
		if (n != c) {
			throw syntaxError("Expected '" + c + "' and instead saw '" + n + "'");
		}
		return n;
	}

	/**
	 * Get the next n characters.
	 *
	 * @param n
	 *            The number of characters to take.
	 * @return A string of n characters.
	 * @throws JSONException
	 *             Substring bounds error if there are not n characters remaining in the source string.
	 */
	public String next(final int n) throws JSONException {
		if (n == 0) {
			return "";
		}

		final char[] chars = new char[n];
		int pos = 0;

		while (pos < n) {
			chars[pos] = this.next();
			if (end()) {
				throw syntaxError("Substring bounds error");
			}
			pos += 1;
		}
		return new String(chars);
	}

	/**
	 * Get the next char in the string, skipping whitespace.
	 *
	 * @throws JSONException
	 *             care for it ...
	 * @return A character, or 0 if there are no more characters.
	 */
	public char nextClean() throws JSONException {
		for (;;) {
			final char c = this.next();
			if (c == 0 || c > ' ') {
				return c;
			}
		}
	}

	/**
	 * Return the characters up to the next close quote character. Backslash processing is done. The formal JSON format
	 * does not allow strings in single quotes, but an implementation is allowed to accept them.
	 *
	 * @param quote
	 *            The quoting character, either <code>"</code> &nbsp;<small>(double quote)</small> or <code>'</code>
	 *            &nbsp;<small>(single quote)</small>.
	 * @return A String.
	 * @throws JSONException
	 *             Unterminated string.
	 */
	public String nextString(final char quote) throws JSONException {
		char c;
		final StringBuffer sb = new StringBuffer();
		for (;;) {
			c = this.next();
			switch (c) {
			case 0:
			case '\n':
			case '\r':
				throw syntaxError("Unterminated string");
			case '\\':
				c = this.next();
				switch (c) {
				case 'b':
					sb.append('\b');
					break;
				case 't':
					sb.append('\t');
					break;
				case 'n':
					sb.append('\n');
					break;
				case 'f':
					sb.append('\f');
					break;
				case 'r':
					sb.append('\r');
					break;
				case 'u':
					sb.append((char) Integer.parseInt(this.next(4), 16));
					break;
				case '"':
				case '\'':
				case '\\':
				case '/':
					sb.append(c);
					break;
				default:
					throw syntaxError("Illegal escape.");
				}
				break;
			default:
				if (c == quote) {
					return sb.toString();
				}
				sb.append(c);
			}
		}
	}

	/**
	 * Get the text up but not including the specified character or the end of line, whichever comes first.
	 *
	 * @param delimiter
	 *            A delimiter character.
	 * @return A string.
	 * @throws JSONException
	 *             care for it ...
	 */
	public String nextTo(final char delimiter) throws JSONException {
		final StringBuffer sb = new StringBuffer();
		for (;;) {
			final char c = this.next();
			if (c == delimiter || c == 0 || c == '\n' || c == '\r') {
				if (c != 0) {
					back();
				}
				return sb.toString().trim();
			}
			sb.append(c);
		}
	}

	/**
	 * Get the text up but not including one of the specified delimiter characters or the end of line, whichever comes
	 * first.
	 *
	 * @param delimiters
	 *            A set of delimiter characters.
	 * @return A string, trimmed.
	 * @throws JSONException
	 *             care for it ...
	 */
	public String nextTo(final String delimiters) throws JSONException {
		char c;
		final StringBuffer sb = new StringBuffer();
		for (;;) {
			c = this.next();
			if (delimiters.indexOf(c) >= 0 || c == 0 || c == '\n' || c == '\r') {
				if (c != 0) {
					back();
				}
				return sb.toString().trim();
			}
			sb.append(c);
		}
	}

	/**
	 * Get the next value. The value can be a Boolean, Double, Integer, JSONArray, JSONObject, Long, or String, or the
	 * JSONObject.NULL object.
	 *
	 * @throws JSONException
	 *             If syntax error.
	 *
	 * @return An object.
	 */
	public Object nextValue() throws JSONException {
		char c = nextClean();
		String string;

		switch (c) {
		case '"':
		case '\'':
			return nextString(c);
		case '{':
			back();
			return new JSONObject(this);
		case '[':
			back();
			return new JSONArray(this);
		}

		/*
		 * Handle unquoted text. This could be the values true, false, or null, or it can be a number. An implementation
		 * (such as this one) is allowed to also accept non-standard forms.
		 *
		 * Accumulate characters until we reach the end of the text or a formatting character.
		 */

		final StringBuffer sb = new StringBuffer();
		while (c >= ' ' && ",:]}/\\\"[{;=#".indexOf(c) < 0) {
			sb.append(c);
			c = this.next();
		}
		back();

		string = sb.toString().trim();
		if (string.equals("")) {
			throw syntaxError("Missing value");
		}
		return JSONObject.stringToValue(string);
	}

	/**
	 * Skip characters until the next character is the requested character. If the requested character is not found, no
	 * characters are skipped.
	 *
	 * @param to
	 *            A character to skip to.
	 * @return The requested character, or zero if the requested character is not found.
	 * @throws JSONException
	 *             care for it ...
	 */
	public char skipTo(final char to) throws JSONException {
		char c;
		try {
			final int startIndex = index;
			final int startCharacter = character;
			final int startLine = line;
			reader.mark(Integer.MAX_VALUE);
			do {
				c = this.next();
				if (c == 0) {
					reader.reset();
					index = startIndex;
					character = startCharacter;
					line = startLine;
					return c;
				}
			} while (c != to);
		} catch (final IOException exc) {
			throw new JSONException(exc);
		}

		back();
		return c;
	}

	/**
	 * Make a JSONException to signal a syntax error.
	 *
	 * @param message
	 *            The error message.
	 * @return A JSONException object, suitable for throwing
	 */
	public JSONException syntaxError(final String message) {
		return new JSONException(message + toString());
	}

	/**
	 * Make a printable string of this JSONTokener.
	 *
	 * @return " at {index} [character {character} line {line}]"
	 */
	@Override
	public String toString() {
		return " at " + index + " [character " + character + " line " + line + "]";
	}
}