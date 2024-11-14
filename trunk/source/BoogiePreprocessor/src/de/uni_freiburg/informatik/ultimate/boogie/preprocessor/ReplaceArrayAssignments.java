/*
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;

/**
 * Replaces array assignments of the form a[i] := e by a := a[i := e]
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ReplaceArrayAssignments extends BoogieTransformer implements IUnmanagedObserver {
	private final BoogiePreprocessorBacktranslator mTranslator;

	protected ReplaceArrayAssignments(final BoogiePreprocessorBacktranslator translator) {
		mTranslator = translator;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// not needed
	}

	@Override
	public void finish() {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof Procedure) {
					final Procedure proc = (Procedure) decl;
					if (proc.getBody() != null) {
						replaceArrayAssignments(proc);
					}
				}
			}
			return false;
		}
		return true;
	}

	private void replaceArrayAssignments(final Procedure proc) {
		final Body body = proc.getBody();
		body.setBlock(processStatements(body.getBlock()));
	}

	private Expression getLHSExpression(final LeftHandSide lhs) {
		Expression expr;
		if (lhs instanceof ArrayLHS) {
			final ArrayLHS arrlhs = (ArrayLHS) lhs;
			final Expression array = getLHSExpression(arrlhs.getArray());
			expr = new ArrayAccessExpression(lhs.getLocation(), lhs.getType(), array, arrlhs.getIndices());
		} else {
			final VariableLHS varlhs = (VariableLHS) lhs;
			expr = new IdentifierExpression(lhs.getLocation(), lhs.getType(), varlhs.getIdentifier(),
					varlhs.getDeclarationInformation());
		}
		return expr;
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		if (statement instanceof AssignmentStatement) {
			final AssignmentStatement assign = (AssignmentStatement) statement;
			final LeftHandSide[] lhs = Arrays.copyOf(assign.getLhs(), assign.getLhs().length);
			final Expression[] rhs = Arrays.copyOf(assign.getRhs(), assign.getRhs().length);
			boolean changed = false;
			for (int i = 0; i < lhs.length; i++) {
				while (lhs[i] instanceof ArrayLHS) {
					final LeftHandSide array = ((ArrayLHS) lhs[i]).getArray();
					final Expression[] indices = ((ArrayLHS) lhs[i]).getIndices();
					final Expression arrayExpr = getLHSExpression(array);
					rhs[i] = new ArrayStoreExpression(lhs[i].getLocation(), array.getType(), arrayExpr, indices,
							rhs[i]);
					lhs[i] = array;
					changed = true;
				}
			}

			if (changed) {
				final AssignmentStatement newAssign = new AssignmentStatement(assign.getLocation(), lhs, rhs);
				ModelUtils.copyAnnotations(assign, newAssign);
				mTranslator.addMapping(assign, newAssign);
				return newAssign;
			}
		}
		return super.processStatement(statement);
	}
}
