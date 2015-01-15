package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;

/**
 * Takes a Boogie ast and filters out all Procedures.
 * Procedures are distinguished between the Procedures using the keyword "procedure" and Procedures with bodies
 * (using the keyword "implementation" or "procedure" with a following body).
 * Note: A Procedure can be both, declaration and implementation! 
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class BoogieProcedureFilter {

	private IUltimateServiceProvider mServices;

	/** All Procedures using the keyword "procedure". Their identifiers are used as keys. */
	private Map<String, Procedure> mDeclarations;
	
	/** All Procedures with bodies. Their identifiers are used as keys. One Procedure can have multiple bodies. */
	private Map<String, Set<Procedure>> mImplementations;

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
	 * If the ast contains multiple declarations (Procedures using the keyword "procedure") with the same identifier or
	 * is missing a declaration for an implementation, then the current tool chain is canceled. This will create an
	 * ErrorResult.
	 * @param astUnit Boogie ast to be filtered.
	 */
	public void filter(Unit astUnit) {
		mDeclarations = new HashMap<String, Procedure>();
		mImplementations = new HashMap<String, Set<Procedure>>();
		for (Declaration decl : astUnit.getDeclarations()) {
			if (decl instanceof Procedure) {
				filterProcedure((Procedure) decl);
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
	 * It is guaranteed, that {@link #getImplementations()} contains a (possibly empty) set of implementations for every
	 * declared procedure.
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
	 * The procedure identifiers are used as keys.
	 * An implementation is a Procedure with a body. This can be both, a Procedure using the keyword "implementation"
	 * or a Procedure using the keyword "procedure" with an attached body.
	 * 
	 * It is guaranteed, that there is a (possibly empty) set of implementations for every procedure in
	 * {@link #getDeclarations()}.
	 *
	 * @return The Procedure implementations.
	 * 
	 * @see #getDeclarations()
	 * @see Procedure#getBody()
	 */
	public Map<String, Set<Procedure>> getImplementations() {
		return mImplementations;
	}
	
	/**
	 * Adds a given Procedure to the right sets: declarations and/or implementations.
	 * @param proc Procedure to be filtered.
	 */
	private void filterProcedure(Procedure proc) {
		Specification[] specs = proc.getSpecification();
		Body body = proc.getBody();
		if (specs != null) {
			addDeclaration(proc);
		}
		if (body != null) {
			addImplementation(proc);
		}
	}

	private void addDeclaration(Procedure declaration) {
		assert declaration.getSpecification() != null;
		Procedure oldEntry = mDeclarations.put(declaration.getIdentifier(), declaration);
		if (oldEntry != null) {
			procedureAlreadyDeclaredError(declaration);
		}
	}
	
	private void addImplementation(Procedure implementation) {
		assert implementation.getBody() != null;
		String procId = implementation.getIdentifier();
		Set<Procedure> implsOfProc = mImplementations.get(procId);
		if (implsOfProc == null) {
			implsOfProc = new HashSet<Procedure>();
			mImplementations.put(procId, implsOfProc);
		}
		implsOfProc.add(implementation);
	}
	
	/**
	 * Adds empty sets of implementations for all declarations without any implementations
	 * and makes the filtered results immutable.
	 */
	private void finishFilteredResults() {
		Set<Procedure> noImplementations = Collections.emptySet();
		for (String procId : mDeclarations.keySet()) {
			if(mImplementations.containsKey(procId)) {
				Set<Procedure> immutableVersion = Collections.unmodifiableSet(mImplementations.get(procId));
				mImplementations.put(procId, immutableVersion);
			} else {				
				mImplementations.put(procId, noImplementations);
			}
		}
		mDeclarations = Collections.unmodifiableMap(mDeclarations);
		mImplementations = Collections.unmodifiableMap(mImplementations);
	}
	
	private void checkForMissingDeclarations() {
		for (String procId : mImplementations.keySet()) {
			if (!mDeclarations.containsKey(procId)) {
				Set<Procedure> implsMissingDecl = mImplementations.get(procId);
				assert !implsMissingDecl.isEmpty();
				missingDeclaration(implsMissingDecl.iterator().next());
			}
		}
	}

	private void procedureAlreadyDeclaredError(Procedure procDecl) {
		String description = "Procedure was already declared: " + procDecl.getIdentifier();
		syntaxError(procDecl.getLocation(), description);
	}

	private void missingDeclaration(Procedure implementation) {
		String description = "Missing declaration for procedure implementation: " + implementation.getIdentifier();
		syntaxError(implementation.getLocation(), description);
	}
	
	/**
	 * Reports a syntax error and cancels the tool chain.
	 * @param syntaxError Syntax error to be reported.
	 */
	private void syntaxError(ILocation location, String description) {
		String pluginId = Activator.PLUGIN_ID;
		mServices.getLoggingService().getLogger(pluginId).error(location + ": " + description);
		mServices.getResultService().reportResult(pluginId, new SyntaxErrorResult(pluginId, location, description));
		mServices.getProgressMonitorService().cancelToolchain();
	}

}
