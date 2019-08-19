/*
 * Copyright (C) 2017 Ben Biesenbach (ben.biesenbach@gmx.de)
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class LoopAccelerationMatrix<INLOC extends IcfgLocation> {

	private final MatrixBB mMatrix;
	private final int mMatrixSize;
	private final UnmodifiableTransFormula mOriginalTransFormula;
	private final ManagedScript mMgScript;
	private final ILogger mLogger;
	private List<Integer> mOpenV = new ArrayList<>();

	public LoopAccelerationMatrix(final ILogger logger, final UnmodifiableTransFormula loopTransFormula, final ManagedScript script) {
		mLogger = logger;
		mMgScript = script;

		mMgScript.lock(this);
		mMgScript.push(this, 1);

		mOriginalTransFormula = loopTransFormula;

		mMatrixSize = mOriginalTransFormula.getInVars().size();
		mMatrix = new MatrixBB(mOriginalTransFormula.getInVars(), logger);

		fillMatrix();
		
		mMgScript.pop(this, 1);
		mMgScript.unlock(this);
	}
	
	private void fillMatrix() {
		// n = 1
		boolean newVectorFound = true;

		final int matrixSize = mOriginalTransFormula.getInVars().size();
		for (int i = 0; i < matrixSize; i++) {
			mOpenV.add(i);
		}
		if(!findInitVector()){
			accelerationFailed();
		}
		while (newVectorFound && !mOpenV.isEmpty()) {
			newVectorFound = false;
			final List<Integer> open = new ArrayList<>();
			for (final int vNumberOpen : mOpenV) {
				Map<Integer, Map<Term, Term>> matrix = new HashMap<>(mMatrix.getMatrix());
				for (Map<Term, Term> closedVector : matrix.values()) {
					if(findVector(closedVector, vNumberOpen)){
						newVectorFound = true;
						break;
					}else{
						open.add(vNumberOpen);
					}
				}
			}
			mOpenV = open;
		}
		if(!find2nVector()){
			accelerationFailed();
		}
	}
	
	private void findSolution(int index){
		final Script script = mMgScript.getScript();
		
		Map<Term, Term> vector = new HashMap<>(mMatrix.getMatrix().get(index));
		final Substitution sub = new Substitution(mMgScript,vector);
		Term transformedTerm = sub.transform(mOriginalTransFormula.getFormula());
		Term closedFormula = UnmodifiableTransFormula.computeClosedFormula(transformedTerm,
				mOriginalTransFormula.getInVars(), mOriginalTransFormula.getOutVars(), new HashSet<>(), mMgScript);
		
		script.push(1);

		try {
			final LBool result = checkSat(script, closedFormula);
			if (result == LBool.SAT) {
				Collection<Term> terms = new ArrayList<>();
				mOriginalTransFormula.getOutVars().entrySet().forEach(outvar -> terms.add(outvar.getKey().getPrimedConstant()));
				final Map<Term, Term> termvar2value = SmtUtils.getValues(script, terms);
				
				Map<Term, Term> m = new HashMap<>();
				mOriginalTransFormula.getOutVars().entrySet().forEach(outvar
						-> m.put(outvar.getValue() , termvar2value.get(outvar.getKey().getPrimedConstant())));
				mMatrix.setSolution(m, index);
			}
		} finally {
			script.pop(1);
		}
	}
	
	private boolean find2nVector(){
		
		Script script = mMgScript.getScript();
		
		Term ogTerm = mOriginalTransFormula.getFormula();
		mOriginalTransFormula.getAuxVars();
		
		Map<IProgramVar, TermVariable> newOutVars = new HashMap<>();
		mOriginalTransFormula.getOutVars().entrySet().forEach(outvar 
				-> newOutVars.put(outvar.getKey(), script.variable(outvar.getValue().toString() + "_n"
						, outvar.getValue().getSort())));
		
		Map<Term, Term> vector = new HashMap<>();
		mOriginalTransFormula.getOutVars().entrySet().forEach(outvar
				-> vector.put(outvar.getValue(), newOutVars.get(outvar.getKey())));
		mOriginalTransFormula.getInVars().entrySet().forEach(invar 
				-> vector.put(invar.getValue(), mOriginalTransFormula.getOutVars().get(invar.getKey())));
		
		final Substitution sub = new Substitution(mMgScript,vector);
		Term newTerm = sub.transform(mOriginalTransFormula.getFormula());
		
		Term fullTerm = script.term("and", ogTerm, newTerm);
		
		Term fullClosedFormula = UnmodifiableTransFormula.computeClosedFormula(fullTerm, 
				mOriginalTransFormula.getInVars(), newOutVars, new HashSet<>(), mMgScript);
		
		script.push(1);
		final LBool result = checkSat(script, fullClosedFormula);
		try {
			if (result == LBool.SAT) {
				Collection<Term> terms = new ArrayList<>();
				mOriginalTransFormula.getInVars().entrySet().forEach(invar -> terms.add(invar.getKey().getDefaultConstant()));
				final Map<Term, Term> termvar2value = SmtUtils.getValues(script, terms);
				mMatrix.setVector(termver2valueTrasformer(termvar2value), mMatrixSize + 1);			
			}
		} finally {
			script.pop(1);
		}
		
		//find2nSolution
		final Substitution subVar = new Substitution(mMgScript,mMatrix.getMatrix().get(mMatrixSize + 1));
		Term transformedFullTerm = subVar.transform(fullTerm);
		Term closedFullTerm = UnmodifiableTransFormula.computeClosedFormula(transformedFullTerm,
				mOriginalTransFormula.getInVars(), newOutVars, new HashSet<>(), mMgScript);
		script.push(1);
		try {
			final LBool resultSolution = checkSat(script, closedFullTerm);
			if (resultSolution == LBool.SAT) {
				Collection<Term> terms = new ArrayList<>();
				newOutVars.entrySet().forEach(outvar -> terms.add(outvar.getKey().getPrimedConstant()));
				final Map<Term, Term> termvar2value = SmtUtils.getValues(script, terms);
				
				Map<Term, Term> m = new HashMap<>();
				mOriginalTransFormula.getOutVars().entrySet().forEach(outvar
						-> m.put(outvar.getValue() , termvar2value.get(outvar.getKey().getPrimedConstant())));
				mMatrix.setSolution(m, mMatrixSize + 1);				
			}
		} finally {
			script.pop(1);
		}
		return result == LBool.SAT;
	}
	
	private boolean findVector(Map<Term, Term> closedVector, int vectorNumber) {
		Map<Term, Term> vector = new HashMap<>(closedVector);
		final Script script = mMgScript.getScript();
		
		final Entry<IProgramVar, TermVariable> openVar = mOriginalTransFormula.getInVars().entrySet().stream().
				collect(Collectors.toList()).get(vectorNumber);

		vector.put(openVar.getValue(), openVar.getKey().getDefaultConstant());
		final Substitution sub = new Substitution(mMgScript,vector);
		Term transformedTerm = sub.transform(mOriginalTransFormula.getFormula());
		transformedTerm = script.term("and", transformedTerm, 
				script.term("distinct", openVar.getKey().getDefaultConstant(), closedVector.get(openVar.getValue())));
		script.push(1);
		
		// TODO muss result in try?
		final LBool result = checkSat(script, transformedTerm);
		try {
			if (result == LBool.SAT) {
				final Map<Term, Term> termvar2value =
						SmtUtils.getValues(script, Collections.singleton(openVar.getKey().getDefaultConstant()));
				vector.put(openVar.getValue(), termvar2value.values().iterator().next());
				mMatrix.setVector(vector, vectorNumber);
				findSolution(vectorNumber);
			}
		} finally {
			script.pop(1);
		}
		return result == LBool.SAT;
	}
	
	private Map<Term, Term> termver2valueTrasformer(Map<Term, Term> termvar2value){
		Map<Term, Term> m = new HashMap<>();
		mOriginalTransFormula.getInVars().entrySet()
		.forEach(invar -> m.put(invar.getValue() , termvar2value.get(invar.getKey().getDefaultConstant())));
		return m;
	}
	
	private boolean findInitVector() {
		final Script script = mMgScript.getScript();
		script.push(1);
		final LBool result = checkSat(script, mOriginalTransFormula.getClosedFormula());
		try {
			if (result == LBool.SAT) {
				Collection<Term> terms = new ArrayList<>();
				mOriginalTransFormula.getInVars().entrySet().forEach(invar -> terms.add(invar.getKey().getDefaultConstant()));
				final Map<Term, Term> termvar2value =
						SmtUtils.getValues(script, terms);
				mMatrix.setVector(termver2valueTrasformer(termvar2value), mMatrixSize);
				findSolution(mMatrixSize);
			}
		} finally {
			script.pop(1);
		}
		return result == LBool.SAT;
	}

	private static LBool checkSat(final Script script, Term term) {
		final TermVariable[] vars = term.getFreeVars();
		final Term[] values = new Term[vars.length];
		for (int i = 0; i < vars.length; i++) {
			values[i] = termVariable2constant(script, vars[i]);
		}
		Term newTerm = script.let(vars, values, term);
		LBool result = script.assertTerm(newTerm);
		if (result == LBool.UNKNOWN) {
			result = script.checkSat();
		}
		return result;
	}
	
	private static Term termVariable2constant(final Script script, final TermVariable tv) {
		final String name = tv.getName() + "_const_" + tv.hashCode();
		script.declareFun(name, Script.EMPTY_SORT_ARRAY, tv.getSort());
		return script.term(name);
	}
	
	private void accelerationFailed(){
		mLogger.info("No acceleration found!");
	}
	
	public MatrixBB getResult(){
		return mMatrix;
	}
}
