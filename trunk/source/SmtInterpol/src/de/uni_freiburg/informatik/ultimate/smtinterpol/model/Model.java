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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.QuantifierTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Coercion;

public class Model implements de.uni_freiburg.informatik.ultimate.logic.Model {
	
	private HashMap<Sort, SortInterpretation> m_Sorts =
		new HashMap<Sort, SortInterpretation>();
	
	private HashMap<FunctionSymbol, ExecTerm> m_FuncVals =
		new HashMap<FunctionSymbol, ExecTerm>();
	
	private Theory m_Theory;
	
	private ModelEvaluator m_Eval;
	
	private FormulaUnLet m_Unlet = new FormulaUnLet(
			FormulaUnLet.UnletType.EXPAND_DEFINITIONS);
	
	private boolean m_PartialModels;
	
	public Model(Clausifier clausifier, Theory t, boolean partial) {
		m_Theory = t;
		m_PartialModels = partial;
		// Extract Boolean model
		Value trueValue = new Value(t.TRUE);
		Value falseValue = new Value(t.FALSE);
		for (BooleanVarAtom atom : clausifier.getBooleanVars()) {
			ApplicationTerm at = (ApplicationTerm) atom.getSMTFormula(t);
			Value value;
			if (atom.getDecideStatus() != null)
				value = atom.getDecideStatus() == atom ? trueValue : falseValue;
			else
				value = atom.getPreferredStatus() == atom ? 
						trueValue : falseValue;
			m_FuncVals.put(at.getFunction(), value);
		}
		// Extract different theories
		CClosure cc = clausifier.getCClosure();
		LinArSolve la = null;
		QuantifierTheory qf = null;
		for (ITheory theory : clausifier.getEngine().getAttachedTheories()) {
			if (theory instanceof LinArSolve)
				la = (LinArSolve) theory;
			else if (theory instanceof QuantifierTheory)
				qf = (QuantifierTheory) theory;
			else if (theory != cc)
				throw new InternalError(
					"Modelproduction for theory not implemented: " + theory);
		}
		SharedTermEvaluator ste = new SharedTermEvaluator(la);
		if (la != null)
			la.fillInModel(this, t, ste);
		if (cc != null)
			cc.fillInModel(this, t, ste);
		if (qf != null)
			qf.fillInModel(this, t, ste);
		m_Eval = new ModelEvaluator(this);
	}
	
	ExecTerm getDefault(ExecTerm term) {
		if (m_PartialModels)
			return new Undefined(term.toSMTLIB(m_Theory, null).getSort());
		return term;
	}
	
	@Override
	public Term evaluate(Term input) {
		Term unletted = m_Unlet.unlet(input);
		return m_Eval.evaluate(unletted);
	}

	@Override
	public Map<Term, Term> evaluate(Term[] input) {
		LinkedHashMap<Term, Term> values = new LinkedHashMap<Term, Term>();
		for (Term t : input)
			values.put(t, evaluate(t));
		return values;
	}
	
	public void extend(FunctionSymbol symb, ExecTerm value) {
		assert(symb.getParameterCount() == 0);
		extendSortInterpretation(symb.getReturnSort(), value);
		if (!m_FuncVals.containsKey(symb)) {
			Term tmp = value.toSMTLIB(symb.getTheory(), null);
			// LIRA hack needed here, too.
			if (tmp.getSort() != symb.getReturnSort()) {
				assert tmp instanceof ConstantTerm;
				ConstantTerm ct = (ConstantTerm) tmp;
				assert ct.getValue() instanceof Rational;
				value = new Value(
						((Rational) ct.getValue()).toTerm(symb.getReturnSort()));
			}
			m_FuncVals.put(symb, value);
		}
//		else
		// This assertion does not hold in LIRA logics since we might have to
		// apply to LIRA-hack to value before comparing...
//			assert (((Value) et).toSMTLIB(null, null) == value);
	}
	
	public void extend(FunctionSymbol symb, ExecTerm[] args, ExecTerm value) {
		if (symb.getParameterCount() == 0)
			extend(symb, value);
		else {
			value = coerce(value, symb.getReturnSort());
			extendSortInterpretation(symb.getReturnSort(), value);
			HashExecTerm het = (HashExecTerm) m_FuncVals.get(symb);
			if (het == null) {
				het = new HashExecTerm(getDefault(value));
				m_FuncVals.put(symb, het);
			}
			het.extend(coerce(symb, args), value);
		}
	}
	
	private ExecTerm coerce(ExecTerm et, Sort expectedSort) {
		Term t = et.toSMTLIB(m_Theory, null);
		if (t.getSort() != expectedSort) {
			assert m_Theory.getLogic().isIRA();
			return new Value(Coercion.coerce(t, expectedSort));
		}
		return et;
	}
	
	private ExecTerm[] coerce(FunctionSymbol fs, ExecTerm[] args) {
		for (int i = 0; i < args.length; ++i)
			args[i] = coerce(args[i], fs.getParameterSort(i));
		return args;
	}

	private void extendSortInterpretation(Sort sort, ExecTerm et) {
		// Don't build an interpretation internal sorts! We know what they are!
		if (sort.isInternal())
			return;
		Term value = et.toSMTLIB(sort.getTheory(), null);
		// Might be violated for internal sorts in LIRA logics 
		assert (value.getSort() == sort);
		SortInterpretation si = m_Sorts.get(sort);
		if (si == null) {
			si = new FiniteSortInterpretation();
			m_Sorts.put(sort, si);
		}
		si.extend(value);
	}
	
	public String toString() {
		ModelFormatter mf = new ModelFormatter();
		if (!m_Sorts.isEmpty())
			mf.appendComment("Sort interpretations");
		for (Map.Entry<Sort, SortInterpretation> me : m_Sorts.entrySet())
			mf.appendSortInterpretation(me.getValue(), me.getKey(), m_Theory);
		// Only if we printed ";; Sort interpretations" we should print the
		// delimiting comment ";; Function interpretations"
		if (!m_Sorts.isEmpty())
			mf.appendComment("Function interpretations");
		for (Map.Entry<FunctionSymbol, ExecTerm> me : m_FuncVals.entrySet())
			if (!me.getKey().isIntern())
				mf.appendValue(me.getKey(), me.getValue(), m_Theory);
		return mf.finish();
	}
	
	Theory getTheory() {
		return m_Theory;
	}

	public ExecTerm getValue(FunctionSymbol fun, ExecTerm[] args) {
		if (fun.isIntern())
			return evalInternalFunction(fun, args);
		return evalExecTerm(fun, args);
	}
		
	private ExecTerm evalExecTerm(FunctionSymbol fun, ExecTerm... args) {
		ExecTerm et = m_FuncVals.get(fun);
		if (et == null) {
			if (m_PartialModels)
				return new Undefined(fun.getReturnSort());
			// We have to dynamically adjust the model here...
			Term value = null;
			Sort returnSort = fun.getReturnSort();
			// Internal sorts get a special value
			if (returnSort.isInternal()) {
				if (returnSort == m_Theory.getBooleanSort())
					value = m_Theory.FALSE;
				else if (returnSort.isNumericSort())
					value = Rational.ZERO.toTerm(returnSort);
				else
					throw new InternalError();
			} else {
				SortInterpretation si = m_Sorts.get(returnSort);
				/*
				 * If we already have an interpretation for this sort, there is
				 * no need to create a new value for this sort.  The function
				 * did not appear in the formula and, hence, is unconstrained.
				 * We can simply peek an element of this sort and use it as the
				 * root element for this function application.
				 * If the sort is not interpreted until now, we have to create
				 * the new sort and the value for this function application.
				 */
				if (si != null)
					value = si.peek();
				if (value == null) {
					Term[] targs = new Term[args.length];
					for (int i = 0; i < args.length; ++i)
						targs[i] = args[i].toSMTLIB(m_Theory, null);
					value = m_Theory.term(fun, targs);
				}
			}
			et = new Value(value);
			extend(fun, args, et);
			return et;
		}
		return et.evaluate(args);
	}
	
	private final Rational rationalValue(ExecTerm t) {
		assert (t instanceof Value);
		return (Rational)((ConstantTerm) t.toSMTLIB(m_Theory, null)).getValue();
	}
	
	private ExecTerm evalInternalFunction(FunctionSymbol fun, ExecTerm[] args) {
		if (fun == m_Theory.TRUE.getFunction())
			return new Value(m_Theory.TRUE);
		if (fun == m_Theory.FALSE.getFunction())
			return new Value(m_Theory.FALSE);
		if (fun == m_Theory.m_And) {
			ExecTerm res = args[0];
			for (ExecTerm arg : args) {
				if (arg.isUndefined())
					res = arg;
				else if (arg.toSMTLIB(m_Theory, null) == m_Theory.FALSE)
					return arg;
				assert (arg.isUndefined() || 
						arg.toSMTLIB(m_Theory, null) == m_Theory.TRUE);
			}
			return res;
		}
		if (fun == m_Theory.m_Or) {
			ExecTerm res = args[0];
			for (ExecTerm arg : args) {
				if (arg.isUndefined())
					res = arg;
				else if (arg.toSMTLIB(m_Theory, null) == m_Theory.TRUE)
					return arg;
				assert (arg.isUndefined() ||
						arg.toSMTLIB(m_Theory, null) == m_Theory.FALSE);
			}
			return res;
		}
		// Propagate undefined
		for (ExecTerm arg : args)
			if (arg.isUndefined())
				return new Undefined(fun.getReturnSort());
		if (fun == m_Theory.m_Implies) {
			assert(args[0] == m_Theory.TRUE || args[0] == m_Theory.FALSE);
			Term val = args[0].toSMTLIB(m_Theory, null);
			for (int i = 1; i < args.length; ++i) {
				Term argi = args[i].toSMTLIB(m_Theory, null);
				assert(argi == m_Theory.TRUE || argi == m_Theory.FALSE);
				val = val == m_Theory.FALSE ? m_Theory.TRUE : 
					argi == m_Theory.TRUE ? m_Theory.TRUE : m_Theory.FALSE;
			}
			return new Value(val);
		}
		if (fun == m_Theory.m_Not) {
			Term arg0 = args[0].toSMTLIB(m_Theory, null);
			assert (args.length == 1 &&
					(arg0 == m_Theory.TRUE || arg0 == m_Theory.FALSE));
			return new Value(
					arg0 == m_Theory.TRUE ? m_Theory.FALSE : m_Theory.TRUE);
		}
		if (fun == m_Theory.m_Xor) {
			Term val = args[0].toSMTLIB(m_Theory, null);
			assert(val == m_Theory.TRUE || val == m_Theory.FALSE);
			for (int i = 1; i < args.length; ++i) {
				Term argi = args[i].toSMTLIB(m_Theory, null);
				assert(argi == m_Theory.TRUE || argi == m_Theory.FALSE);
				val = argi != val ? m_Theory.TRUE : m_Theory.FALSE;
			}
			return new Value(val);
		}
		String name = fun.getName();
		if (name.equals("=")) {
			for (int i = 1; i < args.length; ++i)
				if (!args[i].equals(args[0]))
					return new Value(m_Theory.FALSE);
			return new Value(m_Theory.TRUE);
		}
		if (name.equals("distinct")) {
			HashSet<ExecTerm> vals = new HashSet<ExecTerm>();
			for (ExecTerm arg : args)
				if (!vals.add(arg))
					return new Value(m_Theory.FALSE);
			return new Value(m_Theory.TRUE);
		}
		if (name.equals("ite")) {
			assert(args.length == 3);
			Term selector = args[0].toSMTLIB(m_Theory, null);
			assert(selector == m_Theory.TRUE || selector == m_Theory.FALSE);
			return selector == m_Theory.TRUE ? args[1] : args[2];
		}
		if (name.equals("+")) {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i)
				val = val.add(rationalValue(args[i]));
			return new Value(val.toTerm(fun.getReturnSort()));
		}
		if (name.equals("-")) {
			Rational val = rationalValue(args[0]);
			if (args.length == 1)
				return new Value(val.negate().toTerm(fun.getReturnSort()));
			else {
				for (int i = 1; i < args.length; ++i)
					val = val.sub(rationalValue(args[i]));
				return new Value(val.toTerm(fun.getReturnSort()));
			}
		}
		if (name.equals("*")) {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i)
				val = val.mul(rationalValue(args[i]));
			return new Value(val.toTerm(fun.getReturnSort()));
		}
		if (name.equals("/")) {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				Rational divisor = rationalValue(args[i]);
				if (divisor.equals(Rational.ZERO))
					val = rationalValue(evalExecTerm(
							fun.getTheory().getFunction(
									"@/0", fun.getReturnSort()),
									new Value(val.toTerm(fun.getReturnSort()))));
				else
					val = val.div(divisor);
			}
			return new Value(val.toTerm(fun.getReturnSort()));
		}
		if (name.equals("<=")) {
			for (int i = 1; i < args.length; ++i) {
				Rational arg1 = rationalValue(args[i-1]);
				Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) > 0)
					return new Value(m_Theory.FALSE);
			}
			return new Value(m_Theory.TRUE);
		}
		if (name.equals("<")) {
			for (int i = 1; i < args.length; ++i) {
				Rational arg1 = rationalValue(args[i-1]);
				Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) >= 0)
					return new Value(m_Theory.FALSE);
			}
			return new Value(m_Theory.TRUE);
		}
		if (name.equals(">=")) {
			for (int i = 1; i < args.length; ++i) {
				Rational arg1 = rationalValue(args[i-1]);
				Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) < 0)
					return new Value(m_Theory.FALSE);
			}
			return new Value(m_Theory.TRUE);
		}
		if (name.equals(">")) {
			for (int i = 1; i < args.length; ++i) {
				Rational arg1 = rationalValue(args[i-1]);
				Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) <= 0)
					return new Value(m_Theory.FALSE);
			}
			return new Value(m_Theory.TRUE);
		}
		if (name.equals("div")) {
			// From the standard...
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				Rational n = rationalValue(args[i]);
				if (n.equals(Rational.ZERO))
					val = rationalValue(evalExecTerm(
							fun.getTheory().getFunction(
									"@div0", fun.getReturnSort()),
									new Value(val.toTerm(fun.getReturnSort()))));
				else {
					Rational div = val.div(n);
					val = n.isNegative() ? div.ceil() : div.floor();
				}
			}
			return new Value(val.toTerm(fun.getReturnSort()));
		}
		if (name.equals("mod")) {
			assert(args.length == 2);
			Rational m = rationalValue(args[0]);
			Rational n = rationalValue(args[1]);
			if (n.equals(Rational.ZERO))
				return evalExecTerm(
						fun.getTheory().getFunction(
								"@mod0", fun.getReturnSort()),
								args[0]);
			Rational div = m.div(n);
			div = n.isNegative() ? div.ceil() : div.floor();
			return new Value(m.sub(div.mul(n)).toTerm(fun.getReturnSort()));
		}
		if (name.equals("abs")) {
			assert args.length == 1;
			Rational arg = rationalValue(args[0]);
			return new Value(arg.abs().toTerm(fun.getReturnSort()));
		}
		if (name.equals("divisible")) {
			assert(args.length == 1);
			Rational arg = rationalValue(args[0]);
			BigInteger[] indices = fun.getIndices();
			assert(indices.length == 1);
			Rational rdiv = Rational.valueOf(indices[0], BigInteger.ONE);
			return arg.div(rdiv).isIntegral() ? 
					new Value(m_Theory.TRUE) : new Value(m_Theory.FALSE);
		}
		if (name.equals("to_int")) {
			assert (args.length == 1);
			Rational arg = rationalValue(args[0]);
			return new Value(arg.floor().toTerm(fun.getReturnSort()));
		}
		if (name.equals("to_real")) {
			assert (args.length == 1);
			Rational arg = rationalValue(args[0]);
			return new Value(arg.toTerm(fun.getReturnSort()));
		}
		if (name.equals("is_int")) {
			assert (args.length == 1);
			Rational arg = rationalValue(args[0]);
			return arg.isIntegral() ? 
					new Value(m_Theory.TRUE) : new Value(m_Theory.FALSE);
		}
		if (name.equals("@/0") || name.equals("@div0") || name.equals("@mod0"))
			return evalExecTerm(fun, args);
		throw new AssertionError("Unknown internal function!");
	}

	@Override
	public Term constrainBySort(Term input) {
		SortInterpretation si = m_Sorts.get(input.getSort());
		if (si != null)
			return si.constrain(m_Theory, input);
		// No constraint on this sort.
		return m_Theory.TRUE;
	}

}
