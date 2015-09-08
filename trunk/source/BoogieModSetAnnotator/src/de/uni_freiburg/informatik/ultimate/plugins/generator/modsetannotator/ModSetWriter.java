/*
 * Copyright (C) 2015 Sergio Feo Arenis (arenis@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieModSetAnnotator plug-in.
 * 
 * The ULTIMATE BoogieModSetAnnotator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieModSetAnnotator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieModSetAnnotator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieModSetAnnotator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieModSetAnnotator plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.modsetannotator;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;

public class ModSetWriter implements IUnmanagedObserver {
	private boolean m_PerformedChanges = false;
	private Logger logger;
	private Map<String, Set<String>> m_Modifies;
	private ModSetAnalyzer m_Analyzer;

	public ModSetWriter(ModSetAnalyzer analyzer,
			IUltimateServiceProvider services) {
		logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		m_Analyzer = analyzer;
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex,
			int numberOfModels) throws Throwable {
		m_Modifies = m_Analyzer.getModifiedGlobals();
	}

	@Override
	public void finish() throws Throwable {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean performedChanges() {
		return m_PerformedChanges;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof Unit) {
			Unit unit = (Unit) root;
			Declaration[] declarations = unit.getDeclarations();
			for (int i = 0; i < declarations.length; i++) {
				Declaration d = declarations[i];
				if (d instanceof Procedure) {
					Procedure proc = (Procedure) d;
					Procedure newProc = processProcedure(proc);
					if (newProc != proc) {
						// Replace the declaration if it was modified
						declarations[i] = newProc;
					}
				}
			}
			return false;
		}
		return true;
	}

	/**
	 * Adds variables to the modifies clauses
	 * 
	 * @param decl
	 * @return
	 */
	protected Procedure processProcedure(Procedure proc) {
		Set<String> modifiesSet = m_Modifies.get(proc.getIdentifier());
		// Only process if there is work to do and it is a procedure declaration
		if (modifiesSet != null && proc.getSpecification() != null) {
			// Look for the modifies clause if it exists
			int modSpecPosition = -1;
			VariableLHS[] modifiesArray = null;
			Specification[] specs = proc.getSpecification();

			for (int i = 0; i < specs.length; i++) {
				if (specs[i] instanceof ModifiesSpecification) {
					modifiesArray = ((ModifiesSpecification) specs[i])
							.getIdentifiers();
					modSpecPosition = i;
					break;
				}
			}

			Set<VariableLHS> newModifiesSet = new HashSet<VariableLHS>();

			if (modifiesArray != null) {
				for (VariableLHS var : modifiesArray) {
					newModifiesSet.add(var);
					modifiesSet.remove(var.getIdentifier());
				}
			}

			if (!modifiesSet.isEmpty()) {
				// New variables will be added to the modify clause
				m_PerformedChanges = true;

				for (String var : modifiesSet) {
					VariableLHS newModVar = new VariableLHS(null, var);
					newModifiesSet.add(newModVar);
				}

				ModifiesSpecification newModifies = new ModifiesSpecification(
						proc.getLocation(), false,
						newModifiesSet.toArray(new VariableLHS[newModifiesSet
								.size()]));

				if (modSpecPosition != -1) { // Do the modification in-place
					specs[modSpecPosition] = newModifies;
				} else { // We need a new declaration
					Specification[] newSpec = Arrays.copyOf(specs,
							specs.length + 1);
					newSpec[specs.length] = newModifies;

					Procedure newDecl = new Procedure(proc.getLocation(),
							proc.getAttributes(), proc.getIdentifier(),
							proc.getTypeParams(), proc.getInParams(),
							proc.getOutParams(), newSpec, proc.getBody());

					return newDecl;
				}
			}
		}
		return proc;
	}
}
