/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 * 
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class InterproceduralSequentialComposition extends SequentialComposition implements IInternalAction {

	private static final long serialVersionUID = -1637790156358220366L;

	InterproceduralSequentialComposition(final int serialNumber, final ProgramPoint source,
			final ProgramPoint target, final ManagedScript mgdScript, 
			final ModifiableGlobalVariableManager modGlobVarManager, 
			final boolean simplify, final boolean extPqe, final List<CodeBlock> codeBlocks, 
			final ILogger logger, final IUltimateServiceProvider services,
			final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique, 
			final Boogie2SmtSymbolTable symbolTable) {
		super(serialNumber, source, target, mgdScript, modGlobVarManager, simplify, extPqe, services, codeBlocks, 
				xnfConversionTechnique, simplificationTechnique, symbolTable);
	}

	@Override
	protected void checkNumberOfCallsAndReturns(final int numberCalls, final int  numberReturns) {
		if(numberCalls <= numberReturns) {
			throw new IllegalArgumentException("more calls and returns required");
		}
	}
	
	
	
}
