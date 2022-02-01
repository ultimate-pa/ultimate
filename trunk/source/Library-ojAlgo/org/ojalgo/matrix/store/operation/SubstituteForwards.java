/*
 * Copyright 1997-2015 Optimatika (www.optimatika.se)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package org.ojalgo.matrix.store.operation;

import java.math.BigDecimal;

import org.ojalgo.access.Access2D;
import org.ojalgo.constant.BigMath;
import org.ojalgo.constant.PrimitiveMath;
import org.ojalgo.function.BigFunction;
import org.ojalgo.scalar.ComplexNumber;

public final class SubstituteForwards extends MatrixOperation {

    public static final SubstituteForwards SETUP = new SubstituteForwards();

    public static int THRESHOLD = 64;

    public static void invoke(final BigDecimal[] data, final int structure, final int firstColumn, final int columnLimit, final Access2D<BigDecimal> body,
            final boolean unitDiagonal, final boolean conjugated, final boolean identity) {

        final int tmpDiagDim = (int) Math.min(body.countRows(), body.countColumns());
        final BigDecimal[] tmpBodyRow = new BigDecimal[tmpDiagDim];
        BigDecimal tmpVal;
        int tmpColBaseIndex;

        for (int i = 0; i < tmpDiagDim; i++) {

            for (int j = 0; j <= i; j++) {
                tmpBodyRow[j] = conjugated ? body.get(j, i) : body.get(i, j);
            }

            for (int s = firstColumn; s < columnLimit; s++) {
                tmpColBaseIndex = s * structure;

                tmpVal = BigMath.ZERO;
                for (int j = identity ? s : 0; j < i; j++) {
                    tmpVal = tmpVal.add(tmpBodyRow[j].multiply(data[j + tmpColBaseIndex]));
                }
                if (identity) {
                    tmpVal = i == s ? BigMath.ONE.subtract(tmpVal) : tmpVal.negate();
                } else {
                    tmpVal = data[i + tmpColBaseIndex].subtract(tmpVal);
                }

                if (!unitDiagonal) {
                    tmpVal = BigFunction.DIVIDE.invoke(tmpVal, tmpBodyRow[i]);
                }

                data[i + tmpColBaseIndex] = tmpVal;
            }
        }
    }

    public static void invoke(final ComplexNumber[] data, final int structure, final int firstColumn, final int columnLimit,
            final Access2D<ComplexNumber> body, final boolean unitDiagonal, final boolean conjugated, final boolean identity) {

        final int tmpDiagDim = (int) Math.min(body.countRows(), body.countColumns());
        final ComplexNumber[] tmpBodyRow = new ComplexNumber[tmpDiagDim];
        ComplexNumber tmpVal;
        int tmpColBaseIndex;

        for (int i = 0; i < tmpDiagDim; i++) {

            for (int j = 0; j <= i; j++) {
                tmpBodyRow[j] = conjugated ? body.get(j, i).conjugate() : body.get(i, j);
            }

            for (int s = firstColumn; s < columnLimit; s++) {
                tmpColBaseIndex = s * structure;

                tmpVal = ComplexNumber.ZERO;
                for (int j = identity ? s : 0; j < i; j++) {
                    tmpVal = tmpVal.add(tmpBodyRow[j].multiply(data[j + tmpColBaseIndex]));
                }
                if (identity) {
                    tmpVal = i == s ? ComplexNumber.ONE.subtract(tmpVal) : tmpVal.negate();
                } else {
                    tmpVal = data[i + tmpColBaseIndex].subtract(tmpVal);
                }

                if (!unitDiagonal) {
                    tmpVal = tmpVal.divide(tmpBodyRow[i]);
                }

                data[i + tmpColBaseIndex] = tmpVal;
            }
        }
    }

    public static void invoke(final double[] data, final int structure, final int firstColumn, final int columnLimit, final Access2D<Double> body,
            final boolean unitDiagonal, final boolean conjugated, final boolean identity) {

        final int tmpDiagDim = (int) Math.min(body.countRows(), body.countColumns());
        final double[] tmpBodyRow = new double[tmpDiagDim];
        double tmpVal;
        int tmpColBaseIndex;

        for (int i = 0; i < tmpDiagDim; i++) {

            for (int j = 0; j <= i; j++) {
                tmpBodyRow[j] = conjugated ? body.doubleValue(j, i) : body.doubleValue(i, j);
            }

            for (int s = firstColumn; s < columnLimit; s++) {
                tmpColBaseIndex = s * structure;

                tmpVal = PrimitiveMath.ZERO;
                for (int j = identity ? s : 0; j < i; j++) {
                    tmpVal += tmpBodyRow[j] * data[j + tmpColBaseIndex];
                }
                if (identity) {
                    tmpVal = i == s ? PrimitiveMath.ONE - tmpVal : -tmpVal;
                } else {
                    tmpVal = data[i + tmpColBaseIndex] - tmpVal;
                }

                if (!unitDiagonal) {
                    tmpVal /= tmpBodyRow[i];
                }

                data[i + tmpColBaseIndex] = tmpVal;
            }
        }
    }

    private SubstituteForwards() {
        super();
    }

    @Override
    public int threshold() {
        return THRESHOLD;
    }

}
