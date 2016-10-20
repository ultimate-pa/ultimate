/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * Collects all variables and consts occurring in a set of codeblocks.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class RCFGVariableCollector extends RCFGEdgeVisitor {
	
	private final StatementVariableCollector mStatementVarCollector;
	
	public RCFGVariableCollector(final Set<CodeBlock> blocks) {
		mStatementVarCollector = new StatementVariableCollector();
		collect(blocks);
	}
	
	private void collect(final Set<CodeBlock> blocks) {
		blocks.stream().forEach(this::visit);
	}
	
	@Override
	protected void visit(final StatementSequence c) {
		super.visit(c);
		for (final Statement s : c.getStatements()) {
			mStatementVarCollector.processStatement(s);
		}
	}
	
	@Override
	protected void visit(final Call c) {
		super.visit(c);
		mStatementVarCollector.processStatement(c.getCallStatement());
	}
	
	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private final class StatementVariableCollector extends BoogieVisitor {
		
		@Override
		protected Statement processStatement(final Statement statement) {
			// override because we need the visibility here
			return super.processStatement(statement);
		}
		
		@Override
		protected void visit(final IdentifierExpression expr) {
		}
	}
}