/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Takes a Boogie ast and filters out all Procedures.
 * Procedures are distinguished between the ones using the keyword "procedure" and the ones with bodies
 * (using the keyword "implementation" or "procedure" with a following body).
 * Note: A Procedure can be both, declaration and implementation! 
 * 
 * The filter doesn't support multiple implementations of one procedure, as it is specified in the Boogie standard!
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class BoogieProcedureFilter {

	private final IUltimateServiceProvider mServices;

	/** All Procedures with a (possibly empty) specification. Their identifiers are used as keys. */
	private Map<String, Procedure> mDeclarations;
	
	/** All Procedures with bodies. Their identifiers are used as keys. */
	private Map<String, Procedure> mImplementations;

	/** All non-procedure declarations from the ast unit. */
	private Set<Declaration> mNonProcedureDeclarations;
	
	/**
	 * Creates a new filter.
	 * @param services ServiceProvider for reporting possible errors.
	 */
	public BoogieProcedureFilter(IUltimateServiceProvider services) {
		mServices = services;
	}

	/**
	 * Creates a new filter and applies it on a given ast.
	 * @param services ServiceProvider for reporting possible errors.
	 * @param astUnit Boogie ast to be filtered.
	 * 
	 * @see #filter(Unit)
	 */
	public BoogieProcedureFilter(IUltimateServiceProvider services, Unit astUnit) {
		this(services);
		filter(astUnit);
	}
	
	/**
	 * Filters a Boogie ast.
	 * An ErrorResult will be created and the tool chain will be canceled if...
	 * - there is an implementation without a declaration.
	 * - there are multiple declarations of the same procedure.
	 * - the same procedure has multiple implementations (although this is accepted by the Boogie standard)
	 * 
	 * @param astUnit Boogie ast to be filtered.
	 */
	public void filter(Unit astUnit) {
		mDeclarations = new HashMap<String, Procedure>();
		mImplementations = new HashMap<String, Procedure>();
		mNonProcedureDeclarations = new HashSet<Declaration>();
		for (final Declaration decl : astUnit.getDeclarations()) {
			if (decl instanceof Procedure) {
				filterProcedure((Procedure) decl);
			} else {
				mNonProcedureDeclarations.add(decl);
			}
		}
		finishFilteredResults();
		checkForMissingDeclarations(); // could be disabled
	}
	
	/**
	 * Returns all procedure declarations from the last filtered Boogie ast.
	 * The procedure identifiers are used as keys.
	 * A declaration is a Procedure with a (possibly empty) specification. All declarations use the keyword "procedure".
	 * 
	 * @return The Procedure declarations.
	 * 
	 * @see #getImplementations()
	 * @see Procedure#getSpecification()
	 */
	public Map<String, Procedure> getDeclarations() {
		return mDeclarations;		
	}
	
	/**
	 * Returns all implementations of all procedures from the last filtered Boogie ast.
	 * The procedure identifiers are used as keys. The returned map contains no entries for unimplemented procedures.
	 * It is guaranteed that every key inside the returned map is also present in {@link #getDeclarations()}.
	 * 
	 * An implementation is a Procedure with a body. This can be both, a Procedure using the keyword "implementation"
	 * or a Procedure using the keyword "procedure" with an attached body.
	 *
	 * @return The Procedure implementations.
	 * 
	 * @see #getDeclarations()
	 * @see Procedure#getBody()
	 */
	public Map<String, Procedure> getImplementations() {
		return mImplementations;
	}
	
	/** @return All the declarations from the last filtered Boogie ast, that were no procedures. */
	public Set<Declaration> getNonProcedureDeclarations() {
		return mNonProcedureDeclarations;
	}
	
	/**
	 * Adds a given Procedure to the right sets: declarations and/or implementations.
	 * @param proc Procedure to be filtered.
	 */
	private void filterProcedure(Procedure proc) {
		final Specification[] specs = proc.getSpecification();
		final Body body = proc.getBody();
		if (specs != null) {
			addDeclaration(proc);
		}
		if (body != null) {
			addImplementation(proc);
		}
	}

	private void addDeclaration(Procedure declaration) {
		assert declaration.getSpecification() != null;
		final Procedure oldEntry = mDeclarations.put(declaration.getIdentifier(), declaration);
		if (oldEntry != null) {
			multiDeclarationsError(declaration);
		}
	}
	
	private void addImplementation(Procedure implementation) {
		assert implementation.getBody() != null;
		final Procedure oldEntry = mImplementations.put(implementation.getIdentifier(), implementation);
		if (oldEntry != null) {
			multiImplementationsError(implementation);
		}
	}
	
	/** Makes the filtered results immutable. */
	private void finishFilteredResults() {
		mDeclarations = Collections.unmodifiableMap(mDeclarations);
		mImplementations = Collections.unmodifiableMap(mImplementations);
		mNonProcedureDeclarations = Collections.unmodifiableSet(mNonProcedureDeclarations);
	}
	
	private void checkForMissingDeclarations() {
		for (final String procId : mImplementations.keySet()) {
			if (!mDeclarations.containsKey(procId)) {
				final Procedure implMissingDecl = mImplementations.get(procId);
				missingDeclarationError(implMissingDecl);
			}
		}
	}

	private void multiDeclarationsError(Procedure procDecl) {
		final String description = "Procedure was already declared: " + procDecl.getIdentifier();
		syntaxError(procDecl.getLocation(), description);
	}
	
	private void multiImplementationsError(Procedure procImpl) {
		final String description = "Multiple procedure implementations aren't supported: " + procImpl.getIdentifier();
		unsupportedSyntaxError(procImpl.getLocation(), description);
	}

	private void missingDeclarationError(Procedure implementation) {
		final String description = "Missing declaration for procedure implementation: " + implementation.getIdentifier();
		syntaxError(implementation.getLocation(), description);
	}
	
	private void syntaxError(ILocation location, String description) {
		errorAndAbort(location, description, new SyntaxErrorResult(Activator.PLUGIN_ID, location, description));
	}
	
	private void unsupportedSyntaxError(ILocation location, String description) {
		errorAndAbort(location, description,
				new UnsupportedSyntaxResult<Procedure>(Activator.PLUGIN_ID, location, description));
	}
	
	/**
	 * Prints an error to the log and cancels the tool chain with the given result.
	 * @param location Location of the error.
	 * @param description Description of the error.
	 * @param error Error result.
	 */
	private void errorAndAbort(ILocation location, String description, IResult error) {
		final String pluginId = Activator.PLUGIN_ID;
		mServices.getLoggingService().getLogger(pluginId).error(location + ": " + description);
		mServices.getResultService().reportResult(pluginId, error);
		mServices.getProgressMonitorService().cancelToolchain();
	}

}
