/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ExecTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Value;

public class ModelBuilder {
	
	private static class Delay {
		CCTerm m_Term;
		ExecTerm m_Value;
		public Delay(CCTerm term, ExecTerm value) {
			m_Term = term;
			m_Value = value;
		}
	}
	
	private HashMap<CCTerm, ExecTerm> m_Produced =
			new HashMap<CCTerm, ExecTerm>();
	
	private HashMap<CCTerm, Delay> m_Delayed = new HashMap<CCTerm, Delay>();
	
	private Deque<Delay> m_Todo = new ArrayDeque<Delay>();
	
	public ModelBuilder(List<CCTerm> terms, Model model, Theory t,
			SharedTermEvaluator ste, CCTerm trueNode, CCTerm falseNode) {
		Rational biggest = Rational.MONE;
		Set<CCTerm> delayed = new HashSet<CCTerm>();
		for (CCTerm term : terms) {
			if (term == term.repStar) {
				// Fill value for the whole equivalence class
				Term value = term.getSharedTerm() == null ? term.toSMTTerm(t) :
					ste.evaluate(term.getSharedTerm(), t);
				if (value.getSort().isNumericSort()) {
					// Delay numeral types if value is not shared
					if (!(value instanceof ConstantTerm)) {
						delayed.add(term);
						continue;
					} else {
						Rational v = (Rational) 
							((ConstantTerm) value).getValue();
						biggest = v.compareTo(biggest) > 0 ? v : biggest;
					}
				}
				// Fix Boolean terms
				if (term.repStar == trueNode.repStar)
					value = t.TRUE;
				else if (term.repStar == falseNode.repStar || 
						value.getSort() == t.getBooleanSort())
					// By convention, we convert to == TRUE.  Hence, if a value
					// is not equal to TRUE but Boolean, we have to adjust the
					// model and set it to false.
					value = t.FALSE;
				ExecTerm et = new Value(value);
				for (CCTerm mem : term.members)
					add(model, mem, et, t);
			}
		}
		// Handle all delayed elements
		// We use the smallest integer bigger than biggest
		biggest = biggest.add(Rational.ONE).floor();
		for (CCTerm term : delayed) {
			Term value = biggest.toTerm(term.getFlatTerm().getSort());
			ExecTerm et = new Value(value);
			for (CCTerm mem : term.members)
				add(model, mem, et, t);
			biggest = biggest.add(Rational.ONE);
		}
		finishModel(model, t);
		// no cleanup here since this whole object gets garbage collected anyway
	}
	
	private void add(Model model, CCTerm term, ExecTerm value, Theory t) {
		if (term instanceof CCBaseTerm) {
			CCBaseTerm bt = (CCBaseTerm) term;
			if (!bt.isFunctionSymbol()) {
				// We have to remember the value of the term for applications
				m_Produced.put(term, value);
				return;
			}
			FunctionSymbol symb = bt.getFunctionSymbol();
			if (!symb.isIntern()) {
				model.extend(symb, value);
				m_Produced.put(term, value);
			}
		} else {
			// It is a CCAppTerm
			CCAppTerm app = (CCAppTerm) term;
			assert(!app.isFunc);
			addApp(model, app, value, t);
		}
	}
	
	private void addApp(Model model, CCAppTerm app, ExecTerm value, Theory t) {
		Deque<ExecTerm> args = new ArrayDeque<ExecTerm>();
		CCTerm walk = app;
		boolean enqueued = false;
		while (walk instanceof CCAppTerm) {
			CCAppTerm appwalk = (CCAppTerm) walk;
			ExecTerm val = m_Produced.get(appwalk.getArg());
			if (val == null) {
				if (!enqueued) {
					Delay delay = m_Delayed.get(app);
					if (delay == null) {
						delay = new Delay(app, value);
						m_Delayed.put(app, delay);
					} else
						delay.m_Value = value;
					m_Todo.push(delay);
					enqueued = true;
				}
				Delay delay = m_Delayed.get(appwalk.getArg());
				if (delay == null) {
					delay = new Delay(appwalk.getArg(), null);
					m_Delayed.put(appwalk.getArg(), delay);
				}
				m_Todo.push(delay);
			} else
				args.addFirst(val);
			walk = appwalk.getFunc();
		}
		// Now, walk is the CCBaseTerm corresponding the the function
		// If we did not enqueue an argument, we can extend the model.
		if (!enqueued) {
			FunctionSymbol fs = ((CCBaseTerm) walk).getFunctionSymbol();
			model.extend(fs, args.toArray(new ExecTerm[args.size()]), value);
			m_Produced.put(app, value);
		}
	}
	
	private void finishModel(Model model, Theory t) {
		while (!m_Todo.isEmpty()) {
			Delay d = m_Todo.pop();
			if (!m_Produced.containsKey(d.m_Term)) {
				assert(d.m_Value != null);
				add(model, d.m_Term, d.m_Value, t);
			}
		}
	}
}
