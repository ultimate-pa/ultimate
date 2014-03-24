package de.uni_freiburg.informatik.ultimatetest.util;

import java.util.ArrayList;

import org.junit.Assert;
import org.junit.Test;

public class UtilsTest {

	@Test
	public void indentMultilineStringTest() {
		String s = "Ein String\nso schön\ner geht über 3 Zeilen\nund benutzt irgendeinen Linebreak";
		String indent = "\t\t";
		String lineSeparator = System.getProperty("line.separator");
		String expectedResult = indent + "Ein String" + lineSeparator + indent + "so schön" + lineSeparator + indent
				+ "er geht über 3 Zeilen" + lineSeparator + indent + "und benutzt irgendeinen Linebreak";
		String actualResult = Util.indentMultilineString(s, indent, false).toString();
		Assert.assertEquals(expectedResult, actualResult);

		s = s + "\n";
		actualResult = Util.indentMultilineString(s, indent, true).toString();
		Assert.assertEquals(expectedResult, actualResult);

		expectedResult = expectedResult + lineSeparator;
		actualResult = Util.indentMultilineString(s, indent, false).toString();
		Assert.assertEquals(expectedResult, actualResult);

		s = "Ein einfacher String ohne alles";
		expectedResult = indent + s;
		actualResult = Util.indentMultilineString(s, indent, false).toString();
		Assert.assertEquals(expectedResult, actualResult);
		
		s = "Ein einfacher String ohne alles";
		indent = "";
		expectedResult = s;
		actualResult = Util.indentMultilineString(s, indent, false).toString();
		Assert.assertEquals(expectedResult, actualResult);
	}
	
	@Test
	public void uniformNTest(){
		ArrayList<String> input = new ArrayList<>();
		int size = 100;
		for(int i=0;i<size;++i){
			input.add(String.valueOf(i));
		}
		
		Assert.assertEquals(10, Util.uniformN(input, 10).size());
	}
}
