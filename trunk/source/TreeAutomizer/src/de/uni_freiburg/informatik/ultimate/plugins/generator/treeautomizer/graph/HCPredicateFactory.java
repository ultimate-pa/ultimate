/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public class HCPredicateFactory extends PredicateFactory {

	private ManagedScript mBackendSmtSolverScript;

	public HCPredicateFactory(IUltimateServiceProvider services, ManagedScript mgdScript, IIcfgSymbolTable symbolTable,
			SimplificationTechnique simplificationTechnique, XnfConversionTechnique xnfConversionTechnique) {
		super(services, mgdScript, symbolTable, simplificationTechnique, xnfConversionTechnique);
		mBackendSmtSolverScript = mgdScript;
	}

	
	public HCPredicate createDontCarePredicate(final HornClausePredicateSymbol loc) {
		mBackendSmtSolverScript.lock(this); 
		final HCPredicate result = newPredicate(loc, 
				mBackendSmtSolverScript.term(this, HornUtilConstants.DONTCARE), 
				new HashMap<>());
		mBackendSmtSolverScript.unlock(this); 
		return result;
	}

	public HCPredicate createPredicate(HornClausePredicateSymbol loc) {
		mBackendSmtSolverScript.lock(this); 
		final HCPredicate result = newPredicate(loc, mBackendSmtSolverScript.term(this, loc.toString()), new HashMap<>());
		mBackendSmtSolverScript.unlock(this); 
		return result;
	}

	public HCPredicate truePredicate(HornClausePredicateSymbol loc) {
		mBackendSmtSolverScript.lock(this); 
		final HCPredicate result = newPredicate(loc, mBackendSmtSolverScript.term(this, "true"), new HashMap<>());
		mBackendSmtSolverScript.unlock(this); 
		return result;
	}

	public HCPredicate falsePredicate(HornClausePredicateSymbol loc) {
		mBackendSmtSolverScript.lock(this); 
		final HCPredicate result = newPredicate(loc, mBackendSmtSolverScript.term(this, "false"), new HashMap<>());
		mBackendSmtSolverScript.unlock(this); 
		return result;
	}


	private HCPredicate newPredicate(HornClausePredicateSymbol loc, Term term, Map<Term, HCVar> varsMap) {
		return new HCPredicate(loc, term, varsMap, null);
	}


	public HCPredicate newPredicate(HornClausePredicateSymbol mProgramPoint, int hashCode, Term formula,
			Set<IProgramVar> vars, Map<Term, HCVar> substit) {
		return new HCPredicate(mProgramPoint, hashCode, formula, vars, substit, null);
	}	
}
