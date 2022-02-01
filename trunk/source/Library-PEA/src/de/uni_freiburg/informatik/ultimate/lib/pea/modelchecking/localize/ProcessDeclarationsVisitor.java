/* $Id$
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for Phase Event Automata
 * (PEA).
 * 
 * Copyright (C) 2005-2006, Carl von Ossietzky University of Oldenburg
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */

package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.localize;

import java.io.StringWriter;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.TermToZCDDVisitor;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.ZTerm;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.ZWrapper;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.print.oz.PrintUtils;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;

/**
 * CollectConstantsVisitor visits a Term object and returns a map assigning names of constants to its types.
 * Global and local constants are defined in Z type definitions and it will occur in the constants section of
 * the localize export. If you want a axiomatic definition to occur in the functions part of localize model then
 * it has to be part of the state schema of the class.
 *
 * @author jfaber
 */
public class ProcessDeclarationsVisitor implements
		AxParaVisitor<Map<String, String>>,
		TermVisitor<Map<String, String>>,
		GivenParaVisitor<Map<String, String>> {
	protected Map<String, Integer> freeTypes;
	protected int freeTypeCounter;
	protected ZTerm term;
	protected CDD invariant;
	
	public ProcessDeclarationsVisitor(final ZTerm term) {
		this.term = term;
		freeTypes = new HashMap<>();
		freeTypeCounter = 0;
		invariant = CDD.TRUE;
	}
	
	/*
	 * Visits axiomatic definitions and collects the declared constants and there types.
	 * 
	 * @returns
	 *          a Map<String,String> with variable names as keys and there types as values.
	 * @see net.sourceforge.czt.z.visitor.AxParaVisitor#visitAxPara(net.sourceforge.czt.z.ast.AxPara)
	 */
	@Override
	public Map<String, String> visitAxPara(final AxPara para) {
		final Map<String, String> result = new HashMap<>();
		for (final Decl decl : para.getZSchText().getZDeclList()) {
			if (decl instanceof VarDecl) {
				final StringWriter type = new StringWriter();
				PrintUtils.print(((VarDecl) decl).getExpr(), type, (SectionManager) term.getSectionInfo(),
						ZWrapper.getSectionName(), Markup.UNICODE);
				for (final Name varname : ((VarDecl) decl).getZNameList()) {
					result.put(varname.toString(), type.toString());
				}
			} else {
				final StringWriter failureString = new StringWriter();
				PrintUtils.print(para, failureString, (SectionManager) term.getSectionInfo(),
						ZWrapper.getSectionName(), Markup.UNICODE);
				throw new RuntimeException("Only axiomatic constant definitions " +
						"are supported by the Localize export.\n" +
						"Error while reading in\n\n" + failureString);
			}
		}
		if (para.getZSchText().getPred() != null) {
			final TermToZCDDVisitor cddVisitor = new TermToZCDDVisitor(term);
			invariant = invariant.and(para.getZSchText().getPred().accept(cddVisitor));
		}
		if (result.isEmpty()) {
			return null;
		}
		return result;
	}
	
	/* (non-Javadoc)
	 * @see net.sourceforge.czt.base.visitor.TermVisitor#visitTerm(net.sourceforge.czt.base.ast.Term)
	 */
	@Override
	public Map<String, String> visitTerm(final Term zedObject) {
		final Map<String, String> result = new HashMap<>();
		final Object[] children = zedObject.getChildren();
		for (final Object child : children) {
			if (child instanceof GivenPara) {
				final Map<String, String> newbasicTypes = ((GivenPara) child).accept(this);
				for (final String type : newbasicTypes.keySet()) {
					freeTypes.put(type, freeTypeCounter++);
				}
			} else if (child instanceof Term) {
				final Map<String, String> temp = ((Term) child).accept(this);
				if (temp != null) {
					for (final String var : temp.keySet()) {
						if (result.containsKey(var) &&
								!result.get(var).equals(temp.get(var))) {
							throw new RuntimeException("Different type definitions for" +
									" " + var + "found!");
						}
						result.put(var, temp.get(var));
					}
				}
			}
		}
		if (result.isEmpty()) {
			return null;
		}
		return result;
	}
	
	/*
	 * Visits a basic type definition and collects all basic types into a Map.
	 * 
	 * @returns
	 *          Returns a Map<String,String> with the basic types as keys (and null as values).
	 * 
	 * @see net.sourceforge.czt.z.visitor.GivenParaVisitor#visitGivenPara(net.sourceforge.czt.z.ast.GivenPara)
	 */
	@Override
	public Map<String, String> visitGivenPara(final GivenPara para) {
		final Map<String, String> result = new HashMap<>();
		for (final Name typeName : para.getZNameList()) {
			if (typeName instanceof ZName) {
				result.put(((ZName) typeName).toString(), null);
			}
		}
		return result;
	}
	
	/**
	 * @return Returns the freeTypes.
	 */
	public Map<String, Integer> getFreeTypes() {
		return freeTypes;
	}
	
	/**
	 * @return Returns the invariant.
	 */
	public CDD getInvariant() {
		return invariant;
	}
}
