/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE UnitTest Library.
 * 
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE UnitTest Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.util;

import java.util.ArrayList;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

public class UtilsTest {

	@Test
	public void indentMultilineStringTest() {
		String s = "Ein String\nso schön\ner geht über 3 Zeilen\nund benutzt irgendeinen Linebreak";
		String indent = "\t\t";
		final String lineSeparator = System.getProperty("line.separator");
		String expectedResult = indent + "Ein String" + lineSeparator + indent + "so schön" + lineSeparator + indent
				+ "er geht über 3 Zeilen" + lineSeparator + indent + "und benutzt irgendeinen Linebreak";
		String actualResult = de.uni_freiburg.informatik.ultimate.util.CoreUtil.indentMultilineString(s, indent, false).toString();
		Assert.assertEquals(expectedResult, actualResult);

		s = s + "\n";
		actualResult = de.uni_freiburg.informatik.ultimate.util.CoreUtil.indentMultilineString(s, indent, true).toString();
		Assert.assertEquals(expectedResult, actualResult);

		expectedResult = expectedResult + lineSeparator;
		actualResult = de.uni_freiburg.informatik.ultimate.util.CoreUtil.indentMultilineString(s, indent, false).toString();
		Assert.assertEquals(expectedResult, actualResult);

		s = "Ein einfacher String ohne alles";
		expectedResult = indent + s;
		actualResult = de.uni_freiburg.informatik.ultimate.util.CoreUtil.indentMultilineString(s, indent, false).toString();
		Assert.assertEquals(expectedResult, actualResult);
		
		s = "Ein einfacher String ohne alles";
		indent = "";
		expectedResult = s;
		actualResult = de.uni_freiburg.informatik.ultimate.util.CoreUtil.indentMultilineString(s, indent, false).toString();
		Assert.assertEquals(expectedResult, actualResult);
	}
	
	@Test
	public void uniformNTest(){
		final ArrayList<String> input = new ArrayList<>();
		final int size = 100;
		for(int i=0;i<size;++i){
			input.add(String.valueOf(i));
		}
		Assert.assertEquals(10, TestUtil.uniformN(input, 10).size());
	}
}
