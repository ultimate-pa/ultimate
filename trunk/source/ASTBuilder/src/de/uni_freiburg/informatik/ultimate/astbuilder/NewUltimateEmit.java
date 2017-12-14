/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class NewUltimateEmit extends EmitAstWithVisitors {
	private static final int ONE = 1;
	private static final String LOC = "loc";
	private static final String VISITOR_NAME = "GeneratedBoogieAstVisitor";
	private static final String TRANSFORMER_NAME = "GeneratedBoogieAstTransformer";
	private static final String ROOT_NAME = "BoogieASTNode";

	private static final Set<String> OTHERS =
			new HashSet<>(Arrays.asList(new String[] { VISITOR_NAME, TRANSFORMER_NAME }));

	@Override
	public String getRootConstructorParam(final Node node) {
		if (OTHERS.contains(node.getName())) {
			return super.getRootConstructorParam(node);
		}
		return LOC;
	}

	@Override
	public void emitPreamble(final Node node) {
		super.emitPreamble(node);
		mWriter.println("import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;");
		mWriter.println("import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;");

	}

	@Override
	protected Set<String> getNonClassicNode() {
		return OTHERS;
	}

	@Override
	protected String getVisitorName() {
		return VISITOR_NAME;
	}

	@Override
	protected String getTransformerName() {
		return TRANSFORMER_NAME;
	}

	@Override
	protected String getRootClassName() {
		return ROOT_NAME;
	}

	@Override
	protected boolean isRootSerializable() {
		return true;
	}

	@Override
	public void setGrammar(final Grammar grammar) {
		final List<Entry<String, Node>> parentless = grammar.nodeTable.entrySet().stream()
				.filter(entry -> entry.getValue().getParent() == null).collect(Collectors.toList());
		for (final Entry<String, Node> p : parentless) {
			final Parameter[] oldParams = p.getValue().getParameters();
			final int newLength = oldParams == null ? 1 : (oldParams.length + 1);
			final Parameter[] newParams = new Parameter[newLength];
			if (newLength > ONE) {
				System.arraycopy(oldParams, 0, newParams, 1, newLength - 1);
			}
			newParams[0] = new Parameter(LOC, "ILocation", "the location of this node", true, true, false);
			p.getValue().setParameters(newParams);
		}
		super.setGrammar(grammar);
	}

}
