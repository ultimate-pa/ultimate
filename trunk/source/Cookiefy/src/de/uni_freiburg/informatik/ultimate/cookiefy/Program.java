package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

/**
 * Helper class holding preprocessed input program information
 * @author Jeremi,Vincent
 *
 */
public class Program {
	private final Logger mLogger;
	private Unit m_Unit;
	
	public Map<String, Procedure> Procedures;
	public List<VariableDeclaration> Globals;
	public List<TypeDeclaration> Types;

	/**
	 * Constructs a new program
	 * @param logger 
	 */
	public Program(Logger logger) {
		mLogger = logger;
		Procedures = new LinkedHashMap<String, Procedure>();
		Globals = new LinkedList<VariableDeclaration>();
		Types = new LinkedList<TypeDeclaration>();
		
	}
	
	/**
	 * Constructs a program out of a unit
	 * @param unit
	 * @param logger 
	 */
	public Program(Unit unit, Logger logger) {
		this(logger);
		this.m_Unit = unit;

		for (Declaration decl : unit.getDeclarations()) {
			if (decl instanceof Procedure) {
				Procedure p = (Procedure)decl;
				Procedures.put(p.getIdentifier(), p);
			} else 
			if (decl instanceof VariableDeclaration) {
				Globals.add((VariableDeclaration)decl);
			} else {
				mLogger.warn(
					String.format("Cookiefy does not support this AST element: ", decl.getClass().toString()));
			}
		}
	}
	
	/**
	 * Adds a procedure into the program
	 * @param p
	 */
	public void addProcedure(Procedure p) {
		Procedures.put(p.getIdentifier(), p);
	}
	
	/**
	 * Adds multiple procedures into the program
	 * @param procedures
	 */
	public void addProcedures(Iterable<Procedure> procedures) {
		for (Procedure p : procedures) {
			Procedures.put(p.getIdentifier(), p);
		}
	}
	
	/**
	 * converts this program into a unit
	 * @return
	 */
	public Unit toUnit() {
		List<Declaration> decls = new ArrayList<Declaration>();
		
		for (TypeDeclaration var : Types) {
			decls.add(var);
		}
		
		for (VariableDeclaration var : Globals) {
			decls.add(var);
		}
		
		for (Procedure p : Procedures.values()) {
			decls.add(p);
		}
		
		return new Unit(LocationProvider.getLocation(),decls.toArray(new Declaration[decls.size()]));
	}
}
