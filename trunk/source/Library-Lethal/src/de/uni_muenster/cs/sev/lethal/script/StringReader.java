/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.script;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Helper class for ScriptParser.
 * @author philipp
 *
 */
public class StringReader {

	String string;
	int offset;
	String lastMatch = null;
	
	/**
	 * Creates a new StringReader
	 * @param string String to process.
	 */
	public StringReader(String string){
		this.string = string;
		this.offset = 0;
	}
	
	/**
	 * Returns the char at the current postion of the reader.
	 * @return The char at the current postion of the reader
	 */
	public char currentChar(){
		return this.string.charAt(this.offset);
	}
	
	/**
	 * Returns the substring from the current read pos until the given separator regexp (exclusive)
	 * @param regex expression to find. If regexp contains braces, the match result of them will be stored in this.lastMatch
	 * @return substring from the current read pos until the given separator (exclusive)
	 */
	public String readUntil(String regex){
		Pattern p = Pattern.compile(regex);
		Matcher m = p.matcher(this.string);
		
		String result;
		if (m.find(this.offset)){
			int matchingGroup = 0;
			for (int i = 1; i <= m.groupCount();i++){
				if (m.group(i) != null){
					matchingGroup = i;
					break;
				}
			}
			result = this.string.substring(this.offset, m.start(matchingGroup));
			if (matchingGroup != 0){
				this.lastMatch = m.group(matchingGroup);
			} else {
				this.lastMatch = null;
			}
		} else {
			result = this.string.substring(this.offset);
			this.lastMatch = null;
		}
		return result;
	}
	
	/**
	 * last matching brace expression
   * @return last matching brace expression
   */
	public String lastMatch(){
		return this.lastMatch;
	}
	
	/**
	 * skip while any of the chars of the given string is at the current read pos
	 * @param c list of chars to skip
	 */
	public void skipAll(String c){
		while (this.offset < this.string.length() && (c.indexOf(this.string.charAt(this.offset)) >= 0)){
			this.offset++;
		}
		
	}
	
	/**
	 * Returns true if the string at the current read pos starts equal to the given string.
	 * @param s string to compare to
	 * @return true if the string at the current read pos starts equal to the given string.
	 */
	public boolean startsWith(String s){
		return this.string.startsWith(s, this.offset);
	}
	
	/**
	 * Returns true if the string at the current pos matches the given regexp
	 * @param regex expression to find. If regexp contains braces, the match result of them will be stored in this.lastMatch
	 * @return true if the string at the current pos matches the given regexp
	 */
	public boolean matches(String regex){
		Pattern p = Pattern.compile(regex);
		Matcher m = p.matcher(this.string.substring(this.offset));
		if (m.find()){
			int matchingGroup = 0;
			for (int i = 1; i <= m.groupCount();i++){
				if (m.group(i) != null){
					matchingGroup = i;
					break;
				}
			}
			if (matchingGroup != 0){
				this.lastMatch = m.group(matchingGroup);
			} else {
				this.lastMatch = null;
			}
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Skip the given number of chars in the input
	 * @param count number of chars to skip
	 */
	public void skip(int count){
		this.offset += count;
	}
	
	/**
	 * return the index of the current line.
	 * @return the index of the current line.
	 */
	public int getCurrentLine(){
		int i = this.string.indexOf('\n');
		int line = 1; 
		while (i > 0 && i < this.offset){
			line++;
			i = this.string.indexOf('\n', i+1);
		}
		return line;
	}
	
	/**
	 * Text left to read
	 * @return Text left to read
	 */
	public String remainingText(){
		return this.string.substring(this.offset);
	}
	
	/**
	 * Returns true if we are at the end of the input string
	 * @return true if we are at the end of the input string
	 */
	public boolean eof(){
		return this.offset >= this.string.length();
	}
	
}
