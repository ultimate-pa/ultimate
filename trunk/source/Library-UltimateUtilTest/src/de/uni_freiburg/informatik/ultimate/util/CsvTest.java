/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Util Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Arrays;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils.IExplicitConverter;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class CsvTest {

	@Test
	public void testCsvConvert() {
		final SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "Title" }));
		final SimpleCsvProvider<Long> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "Title" }));

		A.addRow("Row", Arrays.asList(new Integer[] { 1 }));
		B.addRow("Row", Arrays.asList(new Long[] { 1L }));

		final ICsvProvider<Long> something = CsvUtils.convertPerValue(A, new IExplicitConverter<Integer, Long>() {
			@Override
			public Long convert(Integer something) {
				return something.longValue();
			}

		});
		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvFlatten() {
		final SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		final SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A-Row 1", "A-Row 2",
				"B-Row 1", "B-Row 2", "C-Row 1", "C-Row 2" }));
		B.addRow("", Arrays.asList(new Integer[] { 1, 4, 2, 5, 3, 6 }));

		final ICsvProvider<Integer> something = CsvUtils.flatten(A, "-");

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvProject() {
		final SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		final SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A" }));
		B.addRow("Row 1", Arrays.asList(new Integer[] { 1 }));
		B.addRow("Row 2", Arrays.asList(new Integer[] { 4 }));

		final ICsvProvider<Integer> something = CsvUtils.projectColumn(A, "A");

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvProjectEmpty() {
		final SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));

		final SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A" }));

		final ICsvProvider<Integer> something = CsvUtils.projectColumn(A, "A");

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvProjectCollection() {
		final SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		final SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B" }));
		B.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2 }));
		B.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5 }));

		final ICsvProvider<Integer> something = CsvUtils.projectColumn(A, Arrays.asList(new String[] { "A", "B" }));

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvConcatenate() {
		final SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C", "X" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3, 10 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6, 20 }));

		final SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		B.addRow("Row 3", Arrays.asList(new Integer[] { 1, 2, 3 }));
		B.addRow("Row 4", Arrays.asList(new Integer[] { 4, 5, 6 }));

		final SimpleCsvProvider<Integer> C = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C", "X" }));
		C.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3, 10 }));
		C.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6, 20 }));
		C.addRow("Row 3", Arrays.asList(new Integer[] { 1, 2, 3, null }));
		C.addRow("Row 4", Arrays.asList(new Integer[] { 4, 5, 6, null }));

		final ICsvProvider<Integer> something = CsvUtils.concatenateRows(A, B);

		final boolean isEqual = contentAsStringIsEqual(C.getTable(), something.getTable());
		if (!isEqual) {
			System.err.println("B");
			System.err.println(B.toCsv(null, null, true));

			System.err.println("something");
			System.err.println(something.toCsv(null, null, true));
		}

		Assert.assertTrue("something is not equal to B", isEqual);
	}

	@Test
	public void testCsvAddColumn() {
		final SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		final SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B" }));
		B.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2 }));
		B.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5 }));

		final ICsvProvider<Integer> something = CsvUtils.addColumn(B, "C", 2, Arrays.asList(new Integer[] { 3, 6 }));

		final boolean isEqual = contentAsStringIsEqual(A.getTable(), something.getTable());

		Assert.assertTrue("something is not equal to A", isEqual);
	}

	@Test
	public void testCsvTranspose() {
		final SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		final SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "Row 1", "Row 2" }));
		B.addRow("A", Arrays.asList(new Integer[] { 1, 4 }));
		B.addRow("B", Arrays.asList(new Integer[] { 2, 5 }));
		B.addRow("C", Arrays.asList(new Integer[] { 3, 6 }));

		final ICsvProvider<Integer> something = CsvUtils.transpose(A);

		Assert.assertTrue("something is not equal to A", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testWriteCsv() {
		final SimpleCsvProvider<Object> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Object[] { "1", "2,", "" }));
		A.addRow("Row 2", Arrays.asList(new Object[] { "\n", "", null }));

		boolean isOk = true;
		final StringBuilder sb = new StringBuilder();
		try {
			A.toCsv(sb, ",", true);
		} catch (final Exception ex) {
			isOk = false;
		}
		Assert.assertTrue(isOk);
	}

	private <T> boolean contentAsStringIsEqual(List<List<T>> aList, List<List<T>> bList) {
		for (int i = 0; i < aList.size(); ++i) {
			final List<T> rowA = aList.get(i);
			final List<T> rowB = bList.get(i);

			if (rowA.size() != rowB.size()) {
				return false;
			}

			for (int j = 0; j < rowA.size(); ++j) {
				final T entryA = rowA.get(j);
				final T entryB = rowB.get(j);
				if (entryA == null && entryB == null) {
					continue;
				}
				if (entryA != null && entryB != null) {
					if (!entryA.toString().equals(entryB.toString())) {
						return false;
					}
				} else {
					return false;
				}

			}
		}
		return true;
	}

}
