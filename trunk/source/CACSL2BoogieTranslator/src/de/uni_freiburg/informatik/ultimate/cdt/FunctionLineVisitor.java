/*
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * This Visitor produces a HashMap with the Line-Ranges of
 * all Functions. This is necessary to determine the ACSL-Parser Mode.
 * This is global or local.
 */
package de.uni_freiburg.informatik.ultimate.cdt;

import java.util.HashMap;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;

/**
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 30.01.2012
 */
public class FunctionLineVisitor extends ASTVisitor {
	/**
	 * Map startline numbers of a block to end line numbers.
	 */
	private final HashMap<Integer, Integer> mLineRange;

	/**
	 * Standard Constructor.
	 */
	public FunctionLineVisitor() {
		mLineRange = new HashMap<>();
		shouldVisitDeclarations = true;
	}

	@Override
	public int visit(final IASTDeclaration declaration) {
		if (declaration instanceof IASTFunctionDefinition) {
			final IASTFunctionDefinition funcDef = (IASTFunctionDefinition) declaration;
			final int start = funcDef.getFileLocation().getStartingLineNumber();
			final int end = funcDef.getFileLocation().getEndingLineNumber();
			mLineRange.put(start, end);
		}
		return PROCESS_CONTINUE;
	}

	/**
	 * Getter for the line range map, which maps startline numbers of blocks to their end line numbers.
	 *
	 * @return <code>HashMap<Integer, Integer></code> the line ranges of all functions
	 */
	public HashMap<Integer, Integer> getLineRange() {
		return mLineRange;
	}

}
