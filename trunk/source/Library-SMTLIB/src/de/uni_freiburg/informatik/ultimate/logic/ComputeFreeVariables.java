/*
 * Copyright (C) 2009-2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;

/**
 * Helper to compute the free variables contained in a term. This is a very
 * simple term transformer that returns the input term but computes the free
 * variables and sets the corresponding field.
 *
 * @author Jochen Hoenicke
 */
public class ComputeFreeVariables extends NonRecursive {
	static final TermVariable[] NOFREEVARS = new TermVariable[0];

	public ComputeFreeVariables() {
	}

	public void transform(final Term term) {
		enqueueTerm(term);
		run();
	}

	public void enqueueTerm(final Term term) {
		enqueueWalker((final NonRecursive engine) -> walkTerm(term));
	}

	public void walkTerm(final Term term) {
		if (term.mFreeVars != null) {
			return;
		}

		if (term instanceof ConstantTerm) {
			term.mFreeVars = NOFREEVARS;
		} else if (term instanceof TermVariable) {
			term.mFreeVars = new TermVariable[] { (TermVariable) term };
		} else if (term instanceof ApplicationTerm) {
			walkApplicationTerm((ApplicationTerm) term);
		} else if (term instanceof LetTerm) {
			walkLetTerm((LetTerm) term);
		} else if (term instanceof AnnotatedTerm) {
			walkAnnotatedTerm((AnnotatedTerm) term);
		} else if (term instanceof LambdaTerm) {
			walkLambdaTerm((LambdaTerm) term);
		} else if (term instanceof QuantifiedFormula) {
			walkQuantifiedFormula((QuantifiedFormula) term);
		} else if (term instanceof MatchTerm) {
			walkMatchTerm((MatchTerm) term);
		} else {
			throw new AssertionError("Unknown Term");
		}
	}

	public void walkApplicationTerm(final ApplicationTerm appTerm) {
		boolean enqueuedAgain = false;
		for (final Term param : appTerm.getParameters()) {
			if (param.mFreeVars == null) {
				if (!enqueuedAgain) {
					enqueueTerm(appTerm);
					enqueuedAgain = true;
				}
				enqueueTerm(param);
			}
		}

		if (enqueuedAgain) {
			// we need to first compute free vars of child and have enqueued ourselves again
			// afterwards.
			return;
		}

		// Here we compute the free variables of the application term.
		final Term[] params = appTerm.getParameters();
		if (params.length <= 1) {
			if (params.length == 1) {
				appTerm.mFreeVars = params[0].mFreeVars;
			} else {
				appTerm.mFreeVars = ComputeFreeVariables.NOFREEVARS;
			}
		} else {
			int biggestlen = 0;
			int biggestidx = -1;
			for (int i = 0; i < params.length; i++) {
				final TermVariable[] free = params[i].mFreeVars;
				if (free.length > biggestlen) {
					biggestlen = free.length;
					biggestidx = i;
				}
			}
			/* return if term is closed */
			if (biggestidx < 0) {
				appTerm.mFreeVars = ComputeFreeVariables.NOFREEVARS;
			} else {
				List<TermVariable> result = null;
				final List<TermVariable> biggestAsList = Arrays.asList(params[biggestidx].mFreeVars);
				for (int i = 0; i < params.length; i++) {
					if (i == biggestidx) {
						continue;
					}
					final TermVariable[] free = params[i].getFreeVars();
					for (final TermVariable tv : free) {
						if (!biggestAsList.contains(tv)) {
							if (result == null) {
								result = new ArrayList<>();
								result.addAll(biggestAsList);
							}
							if (!result.contains(tv)) {
								result.add(tv);
							}
						}
					}
				}
				if (result == null) {
					appTerm.mFreeVars = params[biggestidx].mFreeVars;
				} else {
					appTerm.mFreeVars = result.toArray(new TermVariable[result.size()]);
				}
			}
		}
	}

	public void walkLetTerm(final LetTerm letTerm) {
		boolean enqueuedAgain = false;
		final Term[] vals = letTerm.getValues();
		for (final Term value : vals) {
			if (value.mFreeVars == null) {
				if (!enqueuedAgain) {
					enqueueTerm(letTerm);
					enqueuedAgain = true;
				}
				enqueueTerm(value);
			}
		}
		final Term body = letTerm.getSubTerm();
		if (body.mFreeVars == null) {
			if (!enqueuedAgain) {
				enqueueTerm(letTerm);
				enqueuedAgain = true;
			}
			enqueueTerm(body);
		}

		if (enqueuedAgain) {
			// we need to first compute free vars of child and have enqueued ourselves again
			// afterwards.
			return;
		}
		final TermVariable[] vars = letTerm.getVariables();
		final HashSet<TermVariable> free = new LinkedHashSet<>();
		free.addAll(Arrays.asList(body.mFreeVars));
		free.removeAll(Arrays.asList(vars));
		for (final Term v : vals) {
			free.addAll(Arrays.asList(v.mFreeVars));
		}
		if (free.isEmpty()) {
			letTerm.mFreeVars = NOFREEVARS;
		} else {
			letTerm.mFreeVars = free.toArray(new TermVariable[free.size()]);
		}
	}

	public void walkLambdaTerm(final LambdaTerm lambdaTerm) {
		final Term body = lambdaTerm.getSubterm();
		if (body.mFreeVars == null) {
			// we need to first compute free vars of child and enqueue ourselves again
			// afterwards.
			enqueueTerm(lambdaTerm);
			enqueueTerm(body);
			return;
		}

		final HashSet<TermVariable> free = new LinkedHashSet<>();
		free.addAll(Arrays.asList(body.mFreeVars));
		free.removeAll(Arrays.asList(lambdaTerm.getVariables()));
		if (free.isEmpty()) {
			lambdaTerm.mFreeVars = NOFREEVARS;
		} else {
			lambdaTerm.mFreeVars = free.toArray(new TermVariable[free.size()]);
		}
	}

	public void walkQuantifiedFormula(final QuantifiedFormula quant) {
		final Term body = quant.getSubformula();
		if (body.mFreeVars == null) {
			// we need to first compute free vars of child and enqueue ourselves again
			// afterwards.
			enqueueTerm(quant);
			enqueueTerm(body);
			return;
		}

		final HashSet<TermVariable> free = new LinkedHashSet<>();
		free.addAll(Arrays.asList(body.mFreeVars));
		free.removeAll(Arrays.asList(quant.getVariables()));
		if (free.isEmpty()) {
			quant.mFreeVars = NOFREEVARS;
		} else {
			quant.mFreeVars = free.toArray(new TermVariable[free.size()]);
		}
	}

	public void walkAnnotatedTerm(final AnnotatedTerm annotTerm) {
		boolean enqueuedAgain = false;
		final HashSet<TermVariable> free = new LinkedHashSet<>();
		final Term body = annotTerm.getSubterm();
		if (body.mFreeVars == null) {
			if (!enqueuedAgain) {
				enqueueTerm(annotTerm);
				enqueuedAgain = true;
			}
			enqueueTerm(body);
		} else {
			free.addAll(Arrays.asList(body.mFreeVars));
		}

		final ArrayDeque<Object> todo = new ArrayDeque<>();
		for (final Annotation annot : annotTerm.getAnnotations()) {
			if (annot.getValue() != null) {
				todo.add(annot.getValue());
			}
		}
		while (!todo.isEmpty()) {
			final Object value = todo.removeLast();
			if (value instanceof Term) {
				final Term subTerm = (Term) value;
				if (subTerm.mFreeVars == null) {
					if (!enqueuedAgain) {
						enqueueTerm(annotTerm);
						enqueuedAgain = true;
					}
					enqueueTerm(subTerm);
				} else if (!enqueuedAgain) {
					free.addAll(Arrays.asList(((Term) value).mFreeVars));
				}
			} else if (value instanceof Object[]) {
				for (final Object elem : (Object[]) value) {
					todo.add(elem);
				}
			}
		}
		if (!enqueuedAgain) {
			if (free.isEmpty()) {
				annotTerm.mFreeVars = NOFREEVARS;
			} else if (free.size() == body.mFreeVars.length) {
				annotTerm.mFreeVars = body.mFreeVars;
			} else {
				annotTerm.mFreeVars = free.toArray(new TermVariable[free.size()]);
			}
		}
	}

	public void walkMatchTerm(final MatchTerm match) {
		boolean enqueuedAgain = false;
		final Term[] cases = match.getCases();
		for (final Term subCase : cases) {
			if (subCase.mFreeVars == null) {
				if (!enqueuedAgain) {
					enqueueTerm(match);
					enqueuedAgain = true;
				}
				enqueueTerm(subCase);
			}
		}
		final Term dataTerm = match.getDataTerm();
		if (dataTerm.mFreeVars == null) {
			if (!enqueuedAgain) {
				enqueueTerm(match);
				enqueuedAgain = true;
			}
			enqueueTerm(dataTerm);
		}

		if (enqueuedAgain) {
			// we need to first compute free vars of child and have enqueued ourselves again
			// afterwards.
			return;
		}
		final HashSet<TermVariable> free = new LinkedHashSet<>();
		for (int i = 0; i < cases.length; i++) {
			final HashSet<TermVariable> freeCase = new LinkedHashSet<>();
			freeCase.addAll(Arrays.asList(cases[i].mFreeVars));
			freeCase.removeAll(Arrays.asList(match.getVariables()[i]));
			free.addAll(freeCase);
		}
		free.addAll(Arrays.asList(dataTerm.mFreeVars));
		if (free.isEmpty()) {
			match.mFreeVars = NOFREEVARS;
		} else if (free.size() == dataTerm.mFreeVars.length) {
			match.mFreeVars = dataTerm.mFreeVars;
		} else {
			match.mFreeVars = free.toArray(new TermVariable[free.size()]);
		}
	}
}
