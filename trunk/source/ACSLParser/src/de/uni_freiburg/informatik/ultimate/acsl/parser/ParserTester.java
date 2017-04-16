/*
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ACSLParser plug-in.
 * 
 * The ULTIMATE ACSLParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ACSLParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ACSLParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ACSLParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ACSLParser plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * Small test for the ACSL Parser.
 */
package de.uni_freiburg.informatik.ultimate.acsl.parser;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * Use this class only for testing purposes.
 * 
 * @author Stefan Wissert
 */
public final class ParserTester {
	private static final int STRING_BUILDER_SIZE = 191;

	private ParserTester() {
		// test class
	}

	/**
	 * @param args
	 *            string arguments.
	 */
	public static void main(final String[] args) {
		final StringBuilder builder = new StringBuilder(STRING_BUILDER_SIZE);
		// @formatter:off
		builder.append("gstart ")
				.append("requires add[1] >= 0 ;")
				.append("assigns \\nothing;")
				.append("ensures -1 <= \\result <= n -1;")
				.append("behavior success:")
				.append("	ensures \\result >= 0 ;")
				.append("behavior failure:")
				.append("	assumes t_is_sorted : x > 0;")
				.append(" 	ensures \\result == -1; ");
		// @formatter:on

		System.out.println(builder.toString());
		try {
			final ACSLNode node = Parser.parseComment(builder.toString(), 0, 0);
			System.out.println(node);
		} catch (final Exception e) {
			e.printStackTrace();
		}
	}
}
