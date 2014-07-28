package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;

/**
 * Objects that stores all global declarations and procedure contracts and makes
 * them available as Collections, Sets, and Maps.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class BoogieDeclarations {
	
	private final Logger mLogger; 

	private final List<Axiom> m_Axioms = 
			new ArrayList<Axiom>();
	private final List<TypeDeclaration> m_TypeDeclarations = 
			new ArrayList<TypeDeclaration>();
	private final List<ConstDeclaration> m_ConstDeclarations = 
			new ArrayList<ConstDeclaration>();
	private final List<FunctionDeclaration> m_FunctionDeclarations = 
			new ArrayList<FunctionDeclaration>();
	private final List<VariableDeclaration> m_GlobalVarDeclarations = 
			new ArrayList<VariableDeclaration>();
	
	
	/**
	 * Maps a procedure name to the Procedure object that contains the
	 * specification of the procedure. 
	 */
	private final Map<String,Procedure> m_ProcSpecification = 
								new HashMap<String,Procedure>();
	
	/**
	 * Maps a procedure name to the Procedure object that contains the
	 * implementation of the procedure. 
	 */	
	private final Map<String,Procedure> m_ProcImplementation = 
								new HashMap<String,Procedure>();
	
	/**
	 * Maps a procedure name to the requires clauses of the procedure
	 */
	private final Map<String,List<RequiresSpecification>> m_Requires = 
								new HashMap<String,List<RequiresSpecification>>();

	/**
	 * Maps a procedure name to the requires clauses of the procedure which are
	 * not free. (A requires clause is not free if we have to proof that it
	 * holds.)
	 */
	private final Map<String,List<RequiresSpecification>> m_RequiresNonFree = 
								new HashMap<String,List<RequiresSpecification>>();

	/**
	 * Maps a procedure name to the ensures clauses of the procedure
	 */
	private final Map<String,List<EnsuresSpecification>> m_Ensures = 
								new HashMap<String,List<EnsuresSpecification>>();
	
	/**
	 * Maps a procedure name to the ensures clauses of the procedure which are
	 * not free. (A ensures clause is not free if we have to proof that it 
	 * holds.)
	 */
	private final Map<String,List<EnsuresSpecification>> m_EnsuresNonFree = 
								new HashMap<String,List<EnsuresSpecification>>();
	
	/**
	 * Maps a procedure name to the set of global variables which may be
	 * modified by the procedure. The set of variables is represented as a map
	 * where the identifier of the variable is mapped to the type of the
	 * variable. 
	 */
	private final Map<String,Set<String>> m_ModifiedVars = 
								new HashMap<String,Set<String>>();
	
	
	public BoogieDeclarations(Unit unit, Logger logger) {
		mLogger = logger;
		for (Declaration decl : unit.getDeclarations()) {
			if (decl instanceof Axiom)
				m_Axioms.add((Axiom) decl);
			else if (decl instanceof TypeDeclaration)
				m_TypeDeclarations.add((TypeDeclaration) decl);
			else if (decl instanceof ConstDeclaration)
				m_ConstDeclarations.add((ConstDeclaration) decl);
			else if (decl instanceof FunctionDeclaration)
				m_FunctionDeclarations.add((FunctionDeclaration) decl);
			else if (decl instanceof VariableDeclaration)
				m_GlobalVarDeclarations.add((VariableDeclaration) decl);
			else if (decl instanceof Procedure) {
				Procedure proc = (Procedure) decl;
				if (proc.getSpecification() != null && proc.getBody() != null) {
					mLogger.info(String.format(
							"Specification and implementation of procedure %s given in one single declaration",
							proc.getIdentifier()));
				}

				if (proc.getSpecification() != null) {
					mLogger.info("Found specification of procedure " + proc.getIdentifier());
					if (m_ProcSpecification.containsKey(proc.getIdentifier())) {
						throw new UnsupportedOperationException("Procedure" + proc.getIdentifier() + "declarated twice");
					} else {
						m_ProcSpecification.put(proc.getIdentifier(), proc);
					}
				}
				if (proc.getBody() != null) {
					mLogger.info("Found implementation of procedure " + proc.getIdentifier());
					if (m_ProcImplementation.containsKey(proc.getIdentifier())) {
						throw new UnsupportedOperationException("File " + "contains two implementations of procedure"
								+ proc.getIdentifier());
					} else {
						m_ProcImplementation.put(proc.getIdentifier(), proc);
					}
				}
			} else
				throw new AssertionError("Unknown Declaration" + decl);
		}
		for (Procedure proc : m_ProcSpecification.values()) {
			extractContract(proc.getIdentifier());
		}
	}

	/**
	 * Get the contract (requires, ensures, modified variables) of a procedure
	 * specification. Write it to m_Ensures, m_EnsuresNonFree, m_Requires,
	 * m_RequiresNonFree and m_ModifiedVars.
	 */
	private void extractContract(String procId) {
		Procedure procSpec = m_ProcSpecification.get(procId);
		Procedure procImpl = m_ProcImplementation.get(procId);
		
		Specification[] specifications;
		if (procSpec != procImpl && procImpl != null) {
			/* Special case where specification and implementation are given by
			 * different procedure objects. In this case we rename the contracts
			 * of the specification to make them compatible with the variables
			 * of the implementation.
			 */
			RenameProcedureSpec renamer = new RenameProcedureSpec();
			specifications = renamer.renameSpecs(procSpec, procImpl);
		} else {
			specifications = procSpec.getSpecification();
		}

		List<EnsuresSpecification> ensures = 
				new ArrayList<EnsuresSpecification>();
		List<EnsuresSpecification> ensuresNonFree = 
				new ArrayList<EnsuresSpecification>();
		List<RequiresSpecification> requires = 
				new ArrayList<RequiresSpecification>();
		List<RequiresSpecification> requiresNonFree = 
				new ArrayList<RequiresSpecification>();
		Set<String> modifiedVars = new HashSet<String>();
		for (Specification spec : specifications) {
			if (spec instanceof EnsuresSpecification) {
				EnsuresSpecification ensSpec = (EnsuresSpecification) spec;
				ensures.add(ensSpec);
				if (!ensSpec.isFree()) {
					ensuresNonFree.add(ensSpec);
				}
			} else if (spec instanceof RequiresSpecification) {
				RequiresSpecification recSpec = (RequiresSpecification) spec;
				requires.add(recSpec);
				if (!recSpec.isFree()) {
					requiresNonFree.add(recSpec);
				}
			} else if (spec instanceof LoopInvariantSpecification) {
				mLogger.debug("Found LoopInvariantSpecification" + spec
						+ "but this plugin does not use loop invariants.");
				throw new IllegalArgumentException(
						"LoopInvariantSpecification may not occur in procedure constract");
			} else if (spec instanceof ModifiesSpecification) {
				ModifiesSpecification modSpec = (ModifiesSpecification) spec;
				for (VariableLHS var : modSpec.getIdentifiers()) {
					String ident = var.getIdentifier();
					modifiedVars.add(ident);
				}
			} else {
				throw new UnsupportedOperationException(
						"Unknown type of specification)");
			}
			m_Ensures.put(procId, ensures);
			m_EnsuresNonFree.put(procId, ensuresNonFree);
			m_Requires.put(procId, requires);
			m_RequiresNonFree.put(procId, requiresNonFree);
			m_ModifiedVars.put(procId, modifiedVars);
		}
	}

	public List<Axiom> getAxioms() {
		return m_Axioms;
	}

	public List<TypeDeclaration> getTypeDeclarations() {
		return m_TypeDeclarations;
	}

	public List<ConstDeclaration> getConstDeclarations() {
		return m_ConstDeclarations;
	}

	public List<FunctionDeclaration> getFunctionDeclarations() {
		return m_FunctionDeclarations;
	}

	public List<VariableDeclaration> getGlobalVarDeclarations() {
		return m_GlobalVarDeclarations;
	}

	public Map<String, Procedure> getProcSpecification() {
		return m_ProcSpecification;
	}

	public Map<String, Procedure> getProcImplementation() {
		return m_ProcImplementation;
	}

	public Map<String, List<RequiresSpecification>> getRequires() {
		return m_Requires;
	}

	public Map<String, List<RequiresSpecification>> getRequiresNonFree() {
		return m_RequiresNonFree;
	}

	public Map<String, List<EnsuresSpecification>> getEnsures() {
		return m_Ensures;
	}

	public Map<String, List<EnsuresSpecification>> getEnsuresNonFree() {
		return m_EnsuresNonFree;
	}

	public Map<String, Set<String>> getModifiedVars() {
		return m_ModifiedVars;
	}
	
	
}
