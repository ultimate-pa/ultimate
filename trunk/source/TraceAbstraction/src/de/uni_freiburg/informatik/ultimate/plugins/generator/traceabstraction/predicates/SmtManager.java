/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class SmtManager {


	private final Boogie2SMT mBoogie2Smt;
	private final ManagedScript mManagedScript;
	private final ModifiableGlobalVariableManager mModifiableGlobals;



	private final PredicateFactory mPredicateFactory;

	public SmtManager(final Boogie2SMT boogie2smt, final ModifiableGlobalVariableManager modifiableGlobals, 
			final IUltimateServiceProvider services,
			final ManagedScript managedScript, final SimplificationTechnique simplificationTechnique, 
			final XnfConversionTechnique xnfConversionTechnique) {
		mBoogie2Smt = boogie2smt;
		mManagedScript = managedScript;
		mModifiableGlobals = modifiableGlobals;
		mPredicateFactory = new PredicateFactory(services, boogie2smt.getManagedScript(), 
				boogie2smt.getBoogie2SmtSymbolTable(), simplificationTechnique, xnfConversionTechnique);
	}


	public PredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}



	public Boogie2SMT getBoogie2Smt() {
		return mBoogie2Smt;
	}

	public Script getScript() {
		return mManagedScript.getScript();
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public ModifiableGlobalVariableManager getModifiableGlobals() {
		return mModifiableGlobals;
	}
	
	


}
