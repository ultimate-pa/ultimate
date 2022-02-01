/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IndexedStatement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;

public class ReachDefBoogieVisitor extends BoogieVisitor {

	private final ReachDefStatementAnnotation mCurrentRD;
	private Statement mCurrentStatement;
	private UnmodifiableTransFormula mCurrentTransFormula;

	private boolean mIsLHS;
	private boolean mIsAssume;
	private ReachDefStatementAnnotation mOldRD;
	private final ScopedBoogieVarBuilder mBuilder;
	private final String mKey;

	public ReachDefBoogieVisitor(ReachDefStatementAnnotation current, ScopedBoogieVarBuilder builder) {
		this(current, builder, null);
	}

	public ReachDefBoogieVisitor(ReachDefStatementAnnotation current, ScopedBoogieVarBuilder builder, String key) {
		assert current != null;
		mCurrentRD = current;
		mBuilder = builder;
		mKey = key;
	}

	public void process(Statement node, UnmodifiableTransFormula transFormula) throws Throwable {
		assert node != null;
		assert mCurrentRD != null;
		mCurrentStatement = node;
		mCurrentTransFormula = transFormula;
		mIsLHS = false;
		mIsAssume = false;
		mOldRD = mCurrentRD.clone();
		processStatement(node);
	}

	@Override
	protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		// TODO: Problem: how do we recognize array recursion?
		mIsLHS = true;
		final LeftHandSide rtr = super.processLeftHandSide(lhs);
		mIsLHS = false;
		return rtr;
	}

	@Override
	protected void visit(VariableLHS lhs) {
		super.visit(lhs);
		updateDef(mBuilder.getScopedBoogieVar(lhs, mCurrentTransFormula), mCurrentStatement);
	}

	@Override
	protected Statement processStatement(Statement statement) {
		mIsAssume = statement instanceof AssumeStatement;
		return super.processStatement(statement);
	}

	@Override
	protected void visit(IdentifierExpression identifier) {
		super.visit(identifier);

		final ScopedBoogieVar current = mBuilder.getScopedBoogieVar(identifier, mCurrentTransFormula);

		if (mIsAssume) {
			// if we are inside an assume, every identifier expression is a use
			// and a def
			updateUse(current);
			updateDef(current, mCurrentStatement);

		} else {
			// if we are not inside an assume, it depends on the side we are on
			if (mIsLHS) {
				updateDef(current, mCurrentStatement);
			} else {
				updateUse(current);
			}
		}
	}

	private void updateDef(ScopedBoogieVar identifier, Statement currentStatement) {
		mCurrentRD.removeAllDefs(identifier);
		mCurrentRD.addDef(identifier, currentStatement, mKey);
	}

	private void updateUse(ScopedBoogieVar id) {
		final Collection<IndexedStatement> stmts = mOldRD.getDef(id);
		if (stmts != null) {
			for (final IndexedStatement stmt : stmts) {
				mCurrentRD.addUse(id, stmt.getStatement(), stmt.getKey());
			}
		}
	}

}
