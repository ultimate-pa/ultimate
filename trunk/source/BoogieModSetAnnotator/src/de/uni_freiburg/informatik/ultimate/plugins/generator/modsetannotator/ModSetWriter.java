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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class ModSetWriter implements IUnmanagedObserver {
	private boolean mPerformedChanges = false;
	private final ILogger mLogger;
	private Map<String, Set<String>> mModifies;
	private final ModSetAnalyzer mAnalyzer;

	public ModSetWriter(ModSetAnalyzer analyzer,
			IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mAnalyzer = analyzer;
	}

	@Override
	public void init(ModelType modelType, int currentModelIndex,
			int numberOfModels) throws Throwable {
		mModifies = mAnalyzer.getModifiedGlobals();
	}

	@Override
	public void finish() throws Throwable {
	}

	@Override
	public boolean performedChanges() {
		return mPerformedChanges;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			final Declaration[] declarations = unit.getDeclarations();
			for (int i = 0; i < declarations.length; i++) {
				final Declaration d = declarations[i];
				if (d instanceof Procedure) {
					final Procedure proc = (Procedure) d;
					final Procedure newProc = processProcedure(proc);
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
		final Set<String> modifiesSet = mModifies.get(proc.getIdentifier());
		// Only process if there is work to do and it is a procedure declaration
		if (modifiesSet != null && proc.getSpecification() != null) {
			// Look for the modifies clause if it exists
			int modSpecPosition = -1;
			VariableLHS[] modifiesArray = null;
			final Specification[] specs = proc.getSpecification();

			for (int i = 0; i < specs.length; i++) {
				if (specs[i] instanceof ModifiesSpecification) {
					modifiesArray = ((ModifiesSpecification) specs[i])
							.getIdentifiers();
					modSpecPosition = i;
					break;
				}
			}

			final Set<VariableLHS> newModifiesSet = new HashSet<VariableLHS>();

			if (modifiesArray != null) {
				for (final VariableLHS var : modifiesArray) {
					newModifiesSet.add(var);
					modifiesSet.remove(var.getIdentifier());
				}
			}

			if (!modifiesSet.isEmpty()) {
				// New variables will be added to the modify clause
				mPerformedChanges = true;

				for (final String var : modifiesSet) {
					final VariableLHS newModVar = new VariableLHS(null, var);
					newModifiesSet.add(newModVar);
				}

				final ModifiesSpecification newModifies = new ModifiesSpecification(
						proc.getLocation(), false,
						newModifiesSet.toArray(new VariableLHS[newModifiesSet
								.size()]));

				if (modSpecPosition != -1) { // Do the modification in-place
					specs[modSpecPosition] = newModifies;
				} else { // We need a new declaration
					final Specification[] newSpec = Arrays.copyOf(specs,
							specs.length + 1);
					newSpec[specs.length] = newModifies;

					final Procedure newDecl = new Procedure(proc.getLocation(),
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
