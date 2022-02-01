/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieExpressionTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.simplifier.NormalFormTransformer;

/**
 * Simplify expressions in assume statements.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class Simplifier extends BaseObserver {

	private final BoogiePreprocessorBacktranslator mTranslator;
	private final NormalFormTransformer<Expression> mSimplifier;

	protected Simplifier(final BoogiePreprocessorBacktranslator translator) {
		mTranslator = translator;
		mSimplifier = new NormalFormTransformer<>(new BoogieExpressionTransformer());
	}

	/**
	 * The process function. Called by the tool-chain and gets a node of the graph as parameter. This function descends
	 * to the unit node and then searches for all procedures and runs unstructureBody on it.
	 */
	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			processUnit(unit);
			return false;
		}
		return true;
	}

	private void processUnit(final Unit unit) {
		final BoogieStatementSimplifier bss = new BoogieStatementSimplifier();
		for (final Declaration decl : unit.getDeclarations()) {
			if (decl instanceof Procedure) {
				final Procedure proc = (Procedure) decl;
				final Body body = proc.getBody();
				if (body == null) {
					continue;
				}
				final Statement[] stmts = body.getBlock();
				if (stmts == null || stmts.length == 0) {
					continue;
				}
				boolean isModified = false;
				final Statement[] newStmts = new Statement[stmts.length];
				int i = 0;
				for (final Statement stmt : stmts) {
					final Statement newStmt = stmt.accept(bss);
					newStmts[i] = newStmt;
					++i;
					isModified |= newStmt != stmt;
				}
				if (isModified) {
					body.setBlock(newStmts);
				}
			}
		}

	}

	private final class BoogieStatementSimplifier extends GeneratedBoogieAstTransformer {
		@Override
		public Statement transform(final AssumeStatement node) {
			final Expression origExpr = node.getFormula();
			final Expression simplExpr = mSimplifier.simplify(origExpr);
			if (origExpr == simplExpr) {
				return node;
			}
			mTranslator.addMapping(origExpr, simplExpr);
			return new AssumeStatement(node.getLoc(), node.getAttributes(), simplExpr);
		}
	}
}
