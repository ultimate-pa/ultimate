/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Print a proof term.
 */
public class PrintProof extends PrintTerm {
	@Override
	public void walkTerm(final Term proof) {
		if (proof instanceof AnnotatedTerm) {
			final AnnotatedTerm annotTerm = (AnnotatedTerm) proof;
			final Annotation[] annots = annotTerm.getAnnotations();
			if (annots.length == 1
					&& (annots[0].getKey() == ProofRules.ANNOT_DEFINE_FUN || annots[0].getKey() == ProofRules.ANNOT_REFINE_FUN)) {
				final Object[] annotVal = (Object[]) annots[0].getValue();
				assert annotVal.length == 2;
				final FunctionSymbol func = (FunctionSymbol) annotVal[0];
				Term definition = (Term) annotVal[1];
				TermVariable[] vars;
				if (definition instanceof LambdaTerm) {
					final LambdaTerm lambda = (LambdaTerm) definition;
					definition = lambda.getSubterm();
					vars = lambda.getVariables();
				} else {
					vars = new TermVariable[0];
				}
				mTodo.add(")");
				mTodo.add(annotTerm.getSubterm());
				mTodo.add(" ");
				mTodo.add(")");
				mTodo.add(definition);
				mTodo.add(") ");
				for (int i = vars.length - 1; i >= 0; i--) {
					mTodo.add(")");
					mTodo.add(vars[i].getSort());
					mTodo.add(" ");
					mTodo.add(vars[i]);
					mTodo.add(i == 0 ? "(" : " (");
				}
				mTodo.add(" (");
				mTodo.add(func.getApplicationString());
				mTodo.add("((" + annots[0].getKey().substring(1) + " ");
				return;
			} else if (annots.length == 1 && annots[0].getKey() == ProofRules.ANNOT_DECLARE_FUN) {
				final Object[] annotVal = (Object[]) annots[0].getValue();
				assert annotVal.length == 1;
				final FunctionSymbol func = (FunctionSymbol) annotVal[0];
				mTodo.add(")");
				mTodo.add(annotTerm.getSubterm());
				mTodo.add(" ");
				mTodo.add(")");
				mTodo.add(func.getReturnSort());
				mTodo.add(") ");
				final Sort[] paramSorts = func.getParameterSorts();
				for (int i = paramSorts.length - 1; i >= 0; i--) {
					mTodo.add(paramSorts[i]);
					if (i > 0) {
						mTodo.add(" ");
					}
				}
				mTodo.add(" (");
				mTodo.add(func.getApplicationString());
				mTodo.add("((" + annots[0].getKey().substring(1) + " ");
				return;
			} else if (annotTerm.getSubterm() instanceof ApplicationTerm
					&& ((ApplicationTerm) annotTerm.getSubterm()).getFunction().getName() == ProofRules.PREFIX + ProofRules.AXIOM) {
				if (annots[0].getKey().equals(ProofRules.ORACLE)) {
					assert annots.length >= 1;
					final Object[] clause = (Object[]) annots[0].getValue();
					mTodo.add(")");
					for (int i = annots.length - 1; i >= 1; i--) {
						if (annots[i].getValue() != null) {
							mTodo.add(annots[i].getValue());
							mTodo.add(" ");
						}
						mTodo.add(annots[i].getKey());
						mTodo.add(" ");
					}
					mTodo.add(clause);
					mTodo.add("(" + annots[0].getKey().substring(1) + " ");
					return;
				} else {
					assert annots.length == 1;
					final Object[] params = (Object[]) annots[0].getValue();
					mTodo.add(")");
					for (int i = params.length - 1; i >= 0; i--) {
						mTodo.add(params[i]);
						mTodo.add(" ");
					}
					mTodo.add("(" + annots[0].getKey().substring(1));
					return;
				}
			}
		}

		if (proof instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) proof;
			final Term[] params = appTerm.getParameters();
			switch (appTerm.getFunction().getName()) {
			case ProofRules.PREFIX + ProofRules.RES: {
				assert params.length == 3;
				mTodo.add(")");
				for (int i = params.length - 1; i >= 0; i--) {
					mTodo.add(params[i]);
					mTodo.add(" ");
				}
				mTodo.add("(" + ProofRules.RES);
				return;
			}
			case ProofRules.PREFIX + ProofRules.CHOOSE: {
				assert params.length == 1;
				final LambdaTerm lambda = (LambdaTerm) params[0];
				assert lambda.getVariables().length == 1;
				mTodo.add(")");
				mTodo.add(lambda.getSubterm());
				mTodo.add(") ");
				mTodo.add(lambda.getVariables()[0].getSort());
				mTodo.add(" ");
				mTodo.add(lambda.getVariables()[0]);
				mTodo.add("(" + ProofRules.CHOOSE + " (");
				return;
			}
			case ProofRules.PREFIX + ProofRules.ASSUME: {
				assert params.length == 1;
				mTodo.add(")");
				mTodo.add(params[0]);
				mTodo.add("(" + ProofRules.ASSUME + " ");
				return;
			}
			default:
				break;
			}
		}

		if (proof instanceof LetTerm) {
			final LetTerm let = (LetTerm) proof;
			final TermVariable[] vars = let.getVariables();
			final Term[] values = let.getValues();
			boolean hasLetProof = false;
			boolean hasLetTerm = false;
			for (int i = 0; i < vars.length; i++) {
				if (ProofRules.isProof(values[i])) {
					hasLetProof = true;
				} else {
					hasLetTerm = true;
				}
			}
			// close parentheses
			if (hasLetTerm) {
				mTodo.addLast(")");
			}
			if (hasLetProof) {
				mTodo.addLast(")");
			}
			// Add subterm to stack.
			mTodo.addLast(let.getSubTerm());
			// add the let-proof for proof variables.
			if (hasLetProof) {
				// Add subterm to stack.
				// Add assigned values to stack
				String sep = ")) ";
				for (int i = values.length - 1; i >= 0; i--) {
					if (ProofRules.isProof(values[i])) {
						mTodo.addLast(sep);
						mTodo.addLast(values[i]);
						mTodo.addLast("(" + vars[i].toString() + " ");
						sep = ") ";
					}
				}
				mTodo.addLast("(let-proof (");
			}
			// add the let for non-proof variables.
			if (hasLetTerm) {
				// Add assigned values to stack
				String sep = ")) ";
				for (int i = values.length - 1; i >= 0; i--) {
					if (!ProofRules.isProof(values[i])) {
						mTodo.addLast(sep);
						mTodo.addLast(values[i]);
						mTodo.addLast("(" + vars[i].toString() + " ");
						sep = ") ";
					}
				}
				mTodo.addLast("(let (");
			}
			return;
		}
		super.walkTerm(proof);
	}
}