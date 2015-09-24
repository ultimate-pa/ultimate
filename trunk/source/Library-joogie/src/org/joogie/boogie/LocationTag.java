/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.boogie;


/**
 * @author schaef
 */
public class LocationTag {

	private StringBuilder commentTag = new StringBuilder();

	private int lineNumber;

	public LocationTag(StringBuilder ctag, int lineno) {
		this.commentTag = ctag;
		this.lineNumber = lineno;
	}
	
	public int getLineNumber() {
		return lineNumber;
	}

	public void addDebugComment(String debugcomment) {
		this.commentTag.append(debugcomment);
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if (commentTag.length() > 0) {
			sb.append("\t // ");
			sb.append(commentTag);
			sb.append("\n");
		}
		return sb.toString();
	}

}
