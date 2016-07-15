/*
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import net.sf.javabdd.BDD;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import net.sf.javabdd.BDDFactory;

/**
 * Some BDD based simplification.
 * TODO: More detailed documentation.
 * @author Michael Steinle
 *
 */
public class SimplifyBdd {
	
	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final ILogger mLogger;
	//TODO: 2016-05-09 Matthias: The following field might be be useless
	private final IFreshTermVariableConstructor mFreshTermVariableConstructor;
	
	public SimplifyBdd(IUltimateServiceProvider services, Script script,
			IFreshTermVariableConstructor freshTermVariableConstructor) {
		super();
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mScript = script;
		mFreshTermVariableConstructor = freshTermVariableConstructor;
	}
	
	/**
	 * Transform input into simplified term. 
	 * @return Term which is logically equivalent to input.
	 */
	public Term transform(final Term input) {
		CollectAtoms ca = new CollectAtoms();
		List<Term> atoms = ca.getTerms(input);
		
		BddBuilder bb = new BddBuilder();
		BDD d = bb.buildBDD(input, atoms);
		
		return bddToTerm(d, atoms);
	}
	
	public Term transformWithImplications(final Term input) {
		CollectAtoms ca = new CollectAtoms();
		List<Term> atoms = ca.getTerms(input);
		
		BddBuilder bb = new BddBuilder();
		BDD d = bb.buildBDD(input, atoms);
		
		return bddToTerm(d, atoms);
	}
	
	private Term bddToTerm(BDD d, List<Term> atoms){
		if(d.isOne()){
			return mScript.term("true");
		}else if(d.isZero()){
			return mScript.term("false");
		}
		
		Term low = bddToTerm(d.low(), atoms);
		Term high = bddToTerm(d.high(), atoms);
		if(low instanceof ApplicationTerm && high instanceof ApplicationTerm && ((ApplicationTerm)low).getFunction().getName().equals("false") && ((ApplicationTerm)high).getFunction().getName().equals("false")){
			return low;
		}else if(high instanceof ApplicationTerm && ((ApplicationTerm)high).getFunction().getName().equals("false")){
			if(low instanceof ApplicationTerm && ((ApplicationTerm)low).getFunction().getName().equals("true")){
				return atoms.get(d.var());
			}else{
				return mScript.term("and", atoms.get(d.var()), mScript.term("not", low));
			}
		}else if(low instanceof ApplicationTerm && ((ApplicationTerm)low).getFunction().getName().equals("false")){
			if(high instanceof ApplicationTerm && ((ApplicationTerm)high).getFunction().getName().equals("true")){
				return atoms.get(d.var());
			}else{
				return mScript.term("and", atoms.get(d.var()), high);
			}
		}
		return (ApplicationTerm)mScript.term("or", 
			mScript.term("and", atoms.get(d.var()), high), 
			mScript.term("and", atoms.get(d.var()), mScript.term("not", low)));
	}
	
	
	public Term transformToDNF(final Term input) {
		CollectAtoms ca = new CollectAtoms();
		List<Term> atoms = ca.getTerms(input);
		
		BddBuilder bb = new BddBuilder();
		BDD d = bb.buildBDD(input, atoms);
		
		List<Term> con = new ArrayList<Term>();
		for(byte[]t:(List<byte[]>)d.allsat()){
			List<Term> lit = new ArrayList<Term>();
			for(int i = 0; i < t.length; i++){
				if(t[i]==0){
					lit.add(SmtUtils.not(mScript, atoms.get(i)));
				}else if(t[i]==1){
					lit.add(atoms.get(i));
				} //==-1 is don't care
			}
			con.add(SmtUtils.and(mScript, lit));
		}
		return SmtUtils.or(mScript, con);
	}
	
	public Term transformToCNF(final Term input) {
		CollectAtoms ca = new CollectAtoms();
		List<Term> atoms = ca.getTerms(input);
		
		BddBuilder bb = new BddBuilder();
		BDD d = bb.buildBDD(input, atoms).not();
		
		List<Term> dis = new ArrayList<Term>();
		for(byte[]t:(List<byte[]>)d.allsat()){
			List<Term> lit = new ArrayList<Term>();
			for(int i = 0; i < t.length; i++){
				if(t[i]==1){
					lit.add(SmtUtils.not(mScript, atoms.get(i)));
				}else if(t[i]==0){
					lit.add(atoms.get(i));
				} //==-1 is don't care
			}
			dis.add(SmtUtils.or(mScript, lit));
		}
		return SmtUtils.and(mScript, dis);
	}
	
	/**
	 * @return true iff the SMT solver was able to prove that t1 implies t2.
	 */
	private boolean implies(Term t1, Term t2) {
		mScript.push(1);
		mScript.assertTerm(t1);
		mScript.assertTerm(SmtUtils.not(mScript, t2));
		final LBool result = mScript.checkSat();
		mScript.pop(1);
		return (result == LBool.UNSAT);
	}
	
	public List<Pair<Term, Term>> impliesPairwise(List<Term> in) {
		List<Pair<Term, Term>> res = new ArrayList<Pair<Term, Term>>();
		
		for (int i = 0; i < in.size(); i++) {
			mScript.push(1);
			mScript.assertTerm(in.get(i));
			for (int j = 0; i < in.size(); i++) {
				mScript.push(1);
				mScript.assertTerm(SmtUtils.not(mScript, in.get(j)));
				final LBool result = mScript.checkSat();
				if(result == LBool.UNSAT){
					res.add(new Pair<Term, Term>(in.get(i), in.get(j)));
				}
				mScript.pop(1);
			}
			mScript.pop(1);
		}
		return res;
	}
}
