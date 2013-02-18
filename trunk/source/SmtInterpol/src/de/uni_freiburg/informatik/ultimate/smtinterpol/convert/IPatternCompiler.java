/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Basic interface for trigger compilers. Reimplement this interface and set the
 * system property <code>de.uni_freiburg.informatik.ultimate.smt.convert.patterncompiler</code> to the
 * fully qualified class name of your pattern compiler to make SmtInterpol load
 * your compiler instead of its default version.
 * @author Juergen Christ
 */
public interface IPatternCompiler {
	/**
	 * Convert one trigger into an instruction sequence.
	 * @param vars			Bound variables.
	 * @param trigger		The trigger. This might be a multi trigger (i.e.,
	 * 						<code>trigger.length > 1</code>) or a unit trigger.
	 * @param converter		The CNF-converter.
	 * @return				Matching instruction sequence data.
	 */
	TriggerData compile(Set<TermVariable> vars,Term[] trigger, ConvertFormula converter);
}
