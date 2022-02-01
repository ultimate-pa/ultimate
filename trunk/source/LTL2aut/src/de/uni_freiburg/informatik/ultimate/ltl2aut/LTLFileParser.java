/*
 * Copyright (C) 2013-2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * 
 * This file is part of the ULTIMATE LTL2Aut plug-in.
 * 
 * The ULTIMATE LTL2Aut plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LTL2Aut plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LTL2Aut plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LTL2Aut plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LTL2Aut plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ltl2aut;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;

/***
 * Transforms the LTL formula in SVComp format to a formula in ACSL_LTL.
 * SVComp format:
    \phi := "P" | \phi || \phi | \phi && \phi | !\phi | G \phi | F \phi |
\phi U \phi | \phi W \phi | \phi R \phi 
	where \phi is a temporal formula and "P" is an atomic proposition.
 * additional comments in the file with "//"
 */
public class LTLFileParser {
	
	private ILogger mLogger;

	
	public LTLFileParser(ILogger logger){
		mLogger = logger;	
	}

	public IElement parse(File file) throws Exception{
		mLogger.info("Using LTL file parser");
		String line = null;
		String ltlProperty = null;
		//get property from file
		try (BufferedReader br = new BufferedReader(new FileReader(file))) {
			while ((line = br.readLine()) != null) {
				if(!line.startsWith("//") && !line.isEmpty()){
					ltlProperty = line;
					break;
				}
			}
		} catch (final IOException e) {
			line = null;
			throw e;
		}
		if (ltlProperty == null){
			throw new RuntimeException("LTL invariant file supplied but no LTL invariant found!");
		}
		
		String formula = transformToACSLComment(ltlProperty);
		//pack into ACSL node
		final ACSLNode node = de.uni_freiburg.informatik.ultimate.acsl.parser.Parser.parseComment(formula, 0, 0);
		if(! (node instanceof GlobalLTLInvariant)){
			throw new RuntimeException("Some ACSL Annotation, but no LTL Invariant found!"); 
		} else {
			mLogger.info("LTLInvariant: " + ((GlobalLTLInvariant)node).getFormula().toString());
		}
		return new ObjectContainer<ACSLNode>(node);
	}
	
	private String transformToACSLComment(String comment){
		String ltlProperty = transformToACSLLTLSyntax(comment);
		final StringBuilder template = new StringBuilder();
		template.append("gstart");
		template.append('\n');
		template.append("ltl invariant positive: ");
		template.append(ltlProperty);
		template.append(";");
		return template.toString();
	}
	
	/***
	 * replace 
	 * "..." -> AP(...)
	 * G -> []
	 * F -> <>
	 * @param formula
	 * @return
	 */
	private String transformToACSLLTLSyntax(String formula){
		final StringBuilder aux = new StringBuilder();
		boolean open = false;
		for(int i = 0; i < formula.length(); i++){
			char c = formula.charAt(i);
			if(c == '\"'){
				if(open){
					aux.append(")");
					open = false;
				} else {
					aux.append("AP(");
					open = true;
				}
			} else {
				aux.append(c);
			}
		}
		assert(!open);
		formula = aux.toString();
		
		formula = formula.replace("G", "[]");
		formula = formula.replace("F", "<>");
		return formula;
	}
	
}



















