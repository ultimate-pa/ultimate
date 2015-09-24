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

package org.joogie.util;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.joogie.boogie.BasicBlock;

import soot.tagkit.LineNumberTag;
import soot.tagkit.SourceLnNamePosTag;
import soot.tagkit.Tag;

/**
 * Class to collect miscellaneous utility functions
 * 
 * @author sergio
 */
public final class Util {
	/**
	 * Reverse a map
	 * 
	 * @param m
	 *            A map (key -> value)
	 * @return The reverse map (value -> key)
	 */
	public static Map<BasicBlock, BasicBlock> reverseMap(
			Map<BasicBlock, BasicBlock> m) {
		Map<BasicBlock, BasicBlock> result = new HashMap<BasicBlock, BasicBlock>();
		for (Entry<BasicBlock, BasicBlock> e : m.entrySet())
			result.put(e.getValue(), e.getKey());
		return result;
	}

	public static Integer runningNumber = 0;

	/**
	 * Finds the line number (tag) in a list of tags
	 * 
	 * @param tags
	 *            List of tags
	 * @return Line number
	 */
	public static int findLineNumber(List<Tag> tags) {
		int lineNumber = 0;
		for (Tag tag : tags) {
			if (tag instanceof LineNumberTag) {
				lineNumber = ((LineNumberTag) tag).getLineNumber();
				break;
			} else if (tag instanceof SourceLnNamePosTag) {
				lineNumber = ((SourceLnNamePosTag) tag).startLn();
				break;
			}
		}
		return lineNumber;
	}

}
