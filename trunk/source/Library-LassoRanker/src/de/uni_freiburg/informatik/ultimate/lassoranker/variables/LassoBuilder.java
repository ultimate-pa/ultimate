/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.Lasso;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableManager;


/**
 * 
 * The LassoBuilder class holds the lasso components during preprocessing.
 * 
 * This object is *not* immutable.
 * 
 * @author Jan Leike
 */
public class LassoBuilder {
	/**
	 * The Boogie2SMT object
	 */
	private final Boogie2SMT m_boogie2smt;
	/**
	 * Table of the created BoogieVarWrapper's such that every BoogieVar
	 * gets at most one wrapper
	 */
	private final Map<BoogieVar, BoogieVarWrapper> m_boogieWrappers;
	
	/**
	 * Collection of all generated replacement TermVariables
	 */
	private final Collection<TermVariable> m_termVariables;
	
	/**
	 * Independent components of the stem transition
	 */
	private Collection<TransFormulaLR> m_stem_components;
	
	/**
	 * Independent components of the loop transition
	 */
	private Collection<TransFormulaLR> m_loop_components;
	
	/**
	 * The script used to create terms in the transition formulas
	 */
	private final Script m_Script;
	
	/**
	 * Object that has to be used for getting and constructing ReplacementVars
	 * that occur in this LassoBuilder.
	 */
	private final ReplacementVarFactory m_ReplacementVarFactory;
	
	/**
	 * Create new (empty) LassoBuilder
	 */
	LassoBuilder(Script script, Boogie2SMT boogie2smt) {
		assert script != null;
		assert boogie2smt != null;
		m_Script = script;
		m_boogie2smt = boogie2smt;
		m_boogieWrappers = new LinkedHashMap<BoogieVar, BoogieVarWrapper>();
		m_termVariables = new ArrayList<TermVariable>();
		m_stem_components = new ArrayList<TransFormulaLR>();
		m_loop_components = new ArrayList<TransFormulaLR>();
		m_ReplacementVarFactory = new ReplacementVarFactory();
		
	}
	
	/**
	 * Create a new LassoBuilder object from components
	 * 
	 * @param script the script that created the transition formulae
	 * @param boogie2smt the boogie smt translator
	 * @param stem the stem transition
	 * @param loop the loop transition
	 */
	public LassoBuilder(Script script, Boogie2SMT boogie2smt, TransFormula stem,
			TransFormula loop) {
		this(script, boogie2smt);
		m_stem_components.add(this.buildTransFormula(stem));
		m_loop_components.add(this.buildTransFormula(loop));
	}
	
	/**
	 * @return the script used to generate the transition formulas
	 */
	public Script getScript() {
		return m_Script;
	}
	
	/**
	 * @return the associated Boogie2SMT object
	 */
	public Boogie2SMT getBoogie2SMT() {
		return m_boogie2smt;
	}
	
	public ReplacementVarFactory getReplacementVarFactory() {
		return m_ReplacementVarFactory;
	}

	/**
	 * @return a collection of all new TermVariable's created with this object
	 */
	public Collection<TermVariable> getGeneratedTermVariables() {
		return Collections.unmodifiableCollection(m_termVariables);
	}
	
	/**
	 * @return the stem's components
	 */
	public Collection<TransFormulaLR> getStemComponents() {
		return m_stem_components;
	}
	
	/**
	 * @return the loop's components
	 */
	public Collection<TransFormulaLR> getLoopComponents() {
		return m_loop_components;
	}
	
	/**
	 * @param stem_components the new stem components
	 */
	public void setStemComponents(Collection<TransFormulaLR> stem_components) {
		m_stem_components = stem_components;
	}
	
	/**
	 * @param loop_components the new loop components
	 */
	public void setLoopComponents(Collection<TransFormulaLR> loop_components) {
		m_loop_components = loop_components;
	}
	
	/**
	 * Wrap BoogieVar's in a one-to-one fashion
	 */
	public RankVar fromBoogieVar(BoogieVar boogieVar) {
		if (m_boogieWrappers.containsKey(boogieVar)) {
			return m_boogieWrappers.get(boogieVar);
		} else {
			BoogieVarWrapper wrapper = new BoogieVarWrapper(boogieVar);
			m_boogieWrappers.put(boogieVar, wrapper);
			return wrapper;
		}
	}
	
	/**
	 * Construct and return a unique term variable with the given name.
	 * The new variable has the same sort as the given Term definition.
	 * @param name an identifier for the variable
	 * @param definition a term that new variable is replacing
	 */
	public TermVariable getNewTermVariable(String name, Sort sort) {
		VariableManager varMan = m_boogie2smt.getVariableManager();
		TermVariable newVar = varMan.constructFreshTermVariable(name, sort);
		m_termVariables.add(newVar);
		return newVar;
	}
	
	/**
	 * Construct a TransFormulaLR from a TransFormula, adding and translating
	 * all existing in- and outVars in the process.
	 * @param transition the TransFormula
	 */
	TransFormulaLR buildTransFormula(TransFormula transition) {
		TransFormulaLR tf = new TransFormulaLR(transition.getFormula());
		
		// Add existing in- and outVars
		for (Map.Entry<BoogieVar, TermVariable> entry
				: transition.getInVars().entrySet()) {
			tf.addInVar(fromBoogieVar(entry.getKey()), entry.getValue());
		}
		for (Map.Entry<BoogieVar, TermVariable> entry
				: transition.getOutVars().entrySet()) {
			tf.addOutVar(fromBoogieVar(entry.getKey()), entry.getValue());
		}
		tf.addAuxVars(transition.getAuxVars());
		
		// Add constant variables as in- and outVars
		for (ApplicationTerm constVar : transition.getConstants()) {
			ReplacementVar repVar = 
					m_ReplacementVarFactory.getOrConstuctReplacementVar(constVar); 
			tf.addInVar(repVar, constVar);
			tf.addOutVar(repVar, constVar);
		}
		return tf;
	}
	
	/**
	 * Run a few sanity checks
	 * @return false if something is fishy
	 */
	public boolean isSane() {
		boolean sane = true;
		for (TransFormulaLR tf : m_stem_components) {
			sane = sane & tf.auxVarsDisjointFromInOutVars();
			sane = sane &
					tf.allAreInOutAux(tf.getFormula().getFreeVars()) == null;
		}
		for (TransFormulaLR tf : m_loop_components) {
			sane = sane & tf.auxVarsDisjointFromInOutVars();
			sane = sane &
					tf.allAreInOutAux(tf.getFormula().getFreeVars()) == null;
		}
		return sane;
	}
	
	/**
	 * Extract the Lasso
	 * 
	 * Only succeeds if the transition formulas are of the required form,
	 * i.e., if preprocessing has been completed.
	 * 
	 * @return the lasso that was built using this LassoBuilder
	 * @throws TermException if the transition formulas are not of the correct
	 *                       form
	 */
	public Lasso getLasso() throws TermException {
		// TODO: For now only one component is supported
		assert m_stem_components.size() == 1;
		assert m_loop_components.size() == 1;
		TransFormulaLR stemTF = m_stem_components.iterator().next();
		TransFormulaLR loopTF = m_loop_components.iterator().next();
		LinearTransition stem = LinearTransition.fromTransFormulaLR(stemTF);
		LinearTransition loop = LinearTransition.fromTransFormulaLR(loopTF);
		return new Lasso(stem, loop);
	}
	
}
