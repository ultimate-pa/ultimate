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

package org.joogie.boogie.util;

import java.util.HashSet;
import java.util.Stack;

import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.util.FileIO;

/**
 * @author schaef
 */
public class BoogieProcedure2Dot {

	public static void toDotFile(BoogieProcedure proc, String dotfile) {
		BasicBlock root = proc.getRootBlock();
		HashSet<BasicBlock> done = new HashSet<BasicBlock>();
		Stack<BasicBlock> todo = new Stack<BasicBlock>();
		todo.push(root);

		while (!todo.empty()) {
			BasicBlock current = todo.pop();
			done.add(current);
			for (BasicBlock suc : current.Successors) {
				if (!todo.contains(suc) && !done.contains(suc))
					todo.add(suc);
			}
		}

		StringBuilder sb = new StringBuilder();

		sb.append("digraph johndoe {\n");
		for (BasicBlock b : done) {			
			for (BasicBlock b_ : b.Successors) {
				sb.append("\"" + block2NodeName(b) + "\"->\"" + block2NodeName(b_)
						+ "\";\n");
			}
		}
		sb.append("}\n");

		FileIO.toFile(sb.toString(), dotfile);
	}
	
	private static String block2NodeName(BasicBlock b) {
		if (b.getLocationTag()==null) {
			return "??::" + b.getName();
		}
		return b.getLocationTag().getLineNumber() + "::" + b.getName();
	}

}
