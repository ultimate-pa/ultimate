package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

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

	private IUltimateServiceProvider mServices;

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
		for (Declaration decl : astUnit.getDeclarations()) {
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
			multiDeclarationsError(declaration);
		}
	}
	
	private void addImplementation(Procedure implementation) {
		assert implementation.getBody() != null;
		Procedure oldEntry = mImplementations.put(implementation.getIdentifier(), implementation);
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
		for (String procId : mImplementations.keySet()) {
			if (!mDeclarations.containsKey(procId)) {
				Procedure implMissingDecl = mImplementations.get(procId);
				missingDeclarationError(implMissingDecl);
			}
		}
	}

	private void multiDeclarationsError(Procedure procDecl) {
		String description = "Procedure was already declared: " + procDecl.getIdentifier();
		syntaxError(procDecl.getLocation(), description);
	}
	
	private void multiImplementationsError(Procedure procImpl) {
		String description = "Multiple procedure implementations aren't supported: " + procImpl.getIdentifier();
		unsupportedSyntaxError(procImpl.getLocation(), description);
	}

	private void missingDeclarationError(Procedure implementation) {
		String description = "Missing declaration for procedure implementation: " + implementation.getIdentifier();
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
		String pluginId = Activator.PLUGIN_ID;
		mServices.getLoggingService().getLogger(pluginId).error(location + ": " + description);
		mServices.getResultService().reportResult(pluginId, error);
		mServices.getProgressMonitorService().cancelToolchain();
	}

}
