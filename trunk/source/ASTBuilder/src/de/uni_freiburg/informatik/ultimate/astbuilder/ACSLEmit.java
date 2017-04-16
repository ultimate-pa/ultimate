/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ASTBuilder plug-in.
 * 
 * The ULTIMATE ASTBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ASTBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ASTBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ASTBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ASTBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.astbuilder;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 * Emitter for the ACSL AST.
 * 
 * @author Markus Lindenmann
 * @since 10.12.2012
 */
public class ACSLEmit extends EmitAstWithVisitors {

	private static final String NAME_VISITOR = "ACSLVisitor";
	private static final String NAME_TRANSFORMER = "ACSLTransformer";
	private static final Set<String> OTHERS =
			new HashSet<>(Arrays.asList(new String[] { NAME_VISITOR, NAME_TRANSFORMER }));

	@Override
	protected Set<String> getNonClassicNode() {
		return OTHERS;
	}

	@Override
	protected String getVisitorName() {
		return NAME_VISITOR;
	}

	@Override
	protected String getTransformerName() {
		return NAME_TRANSFORMER;
	}

	@Override
	protected String getRootClassName() {
		return "ACSLNode";
	}

	@Override
	public void emitPreamble(final Node node) {
		super.emitPreamble(node);
		mWriter.println("import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;");
	}

}
