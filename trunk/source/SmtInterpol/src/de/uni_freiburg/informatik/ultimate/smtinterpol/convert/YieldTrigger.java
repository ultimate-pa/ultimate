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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.TriggerExecutionContext;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;


// We do not need to track bound variables for skolemization since we always use a new skolem constant...

/**
 * A yield instruction.
 * @author Jochen Hoenicke, Juergen Christ
 */
public class YieldTrigger extends CCTrigger {
	protected ConvertFormula converter;
	private ScopedHashMap<TermVariable,FlatTerm> m_LetTable;
	// Quantifier proxy literal
	private Literal quantlit;
	// subform of the quantifier
	protected Term quantsub;
	// Substitution
	Map<TermVariable, Integer> substitution;
	// Prevent substituting the same term multiple times
	InstantiationUnifier knownSubsts;
	
	/**
	 * Create a new yield instruction
	 * @param subst		Substitution map specifying for each variable a register
	 * 					index.
	 */
	public YieldTrigger(Map<TermVariable,Integer> subst) {
		super();
		quantlit = null;
		substitution = subst;
	}
	
	/**
	 * Called by the converter to set some final properties.
	 */
	public void postInit(ConvertFormula converter,
			Map<TermVariable, FlatTerm> letTable,Term sub,
			InstantiationUnifier unifier) {
		assert sub.getSort() == converter.getTheory().getBooleanSort() : 
			"Non-Boolean sub formula in quantifier";
		this.converter = converter;
		this.m_LetTable = new ScopedHashMap<TermVariable, FlatTerm>();
		this.m_LetTable.putAll(letTable);
		quantsub = sub;
		assert(checkSubstitution());
		knownSubsts = unifier;
	}
	
	private boolean checkSubstitution() {
		for (TermVariable tv : quantsub.getFreeVars()) {
			if (!substitution.containsKey(tv))
				return false;
		}
		return true;
	}
	
	public void setProxyLiteral(Literal lit) {
		quantlit = lit;
	}
	
	protected void instantiate(CCTerm[] regs) {
		converter.letTable.beginScope();
		try {
			for (Entry<TermVariable, Integer> me : substitution.entrySet()) {
				assert (regs[me.getValue()].getFlatTerm() != null);
//				converter.letTable.put(me.getKey(),regs[me.getValue()].getFlatTerm());
			}
			FlatFormula ff = converter.convertFormula(quantsub);
			// Guard against true
			if (ff == converter.TRUE)
				return;
			converter.cclosure.instantiation();
			if (quantlit == null) {
				// Match at the top level ==> add ff at top level
				// TODO: Proof production for interpolation
				converter.dpllEngine.topLevelMatch();
				ff.addAsAxiom(null);
			} else {
				Collection<FlatFormula> subs = ff.getSubFormulas();
				Literal[] lits = new Literal[subs.size()+1];
				int i = 0;
				lits[i] = quantlit.negate();
				for (FlatFormula sub : ff.getSubFormulas()) {
					lits[++i] = sub.getLiteral();
				}
//				converter.dpllEngine.addInstantiationClause(lits);
			}
		} finally {
			converter.letTable.endScope();
		}
	}
	
	@Override
	public void match(CClosure engine,CCTerm[] regs,List<CCTrigger> path,
			int pos,TriggerExecutionContext tec,Deque<Object> unused) {
		assert(tec != null);
		// Do the "reactivation check" here
		if (tec.isPassive())
			return;
		tec.passivate();
		engine.yieldDone(tec);
		if (!knownSubsts.createInstantiation(regs, substitution,
				converter.dpllEngine.getLogger(),quantsub))
			return;
		instantiate(regs);
	}

	@Override
	public CCTrigger next() {
		throw new InternalError("next on YieldTrigger???");
	}

	@Override
	public String toString() {
		return "Yield " + quantsub + " with " + substitution;
	}

	@Override
	public int computeNumLiveRegisters() {
		int num = 0;
		for (int regnum : substitution.values()) {
			if (regnum > num)
				num = regnum;
		}
		return num + 1;
	}

	@Override
	public boolean getsCandidates() {
		return false;
	}

}
