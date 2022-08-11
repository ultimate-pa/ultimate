/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.commons.lang3.builder;

import java.io.Serializable;
import java.lang.reflect.Array;
import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.WeakHashMap;

import org.apache.commons.lang3.ClassUtils;
import org.apache.commons.lang3.ObjectUtils;
import org.apache.commons.lang3.StringEscapeUtils;
import org.apache.commons.lang3.StringUtils;

/**
 * <p>Controls {@code String} formatting for {@link ToStringBuilder}.
 * The main public interface is always via {@code ToStringBuilder}.</p>
 *
 * <p>These classes are intended to be used as {@code Singletons}.
 * There is no need to instantiate a new style each time. A program
 * will generally use one of the predefined constants on this class.
 * Alternatively, the {@link StandardToStringStyle} class can be used
 * to set the individual settings. Thus most styles can be achieved
 * without subclassing.</p>
 *
 * <p>If required, a subclass can override as many or as few of the
 * methods as it requires. Each object type (from {@code boolean}
 * to {@code long} to {@code Object} to {@code int[]}) has
 * its own methods to output it. Most have two versions, detail and summary.
 *
 * <p>For example, the detail version of the array based methods will
 * output the whole array, whereas the summary method will just output
 * the array length.</p>
 *
 * <p>If you want to format the output of certain objects, such as dates, you
 * must create a subclass and override a method.
 * </p>
 * <pre>
 * public class MyStyle extends ToStringStyle {
 *   protected void appendDetail(StringBuffer buffer, String fieldName, Object value) {
 *     if (value instanceof Date) {
 *       value = new SimpleDateFormat("yyyy-MM-dd").format(value);
 *     }
 *     buffer.append(value);
 *   }
 * }
 * </pre>
 *
 * @since 1.0
 */
@SuppressWarnings("deprecation") // StringEscapeUtils
public abstract class ToStringStyle implements Serializable {

    /**
     * Serialization version ID.
     */
    private static final long serialVersionUID = -2587890625525655916L;

    /**
     * The default toString style. Using the {@code Person}
     * example from {@link ToStringBuilder}, the output would look like this:
     *
     * <pre>
     * Person@182f0db[name=John Doe,age=33,smoker=false]
     * </pre>
     */
    public static final ToStringStyle DEFAULT_STYLE = new DefaultToStringStyle();

    /**
     * The multi line toString style. Using the {@code Person}
     * example from {@link ToStringBuilder}, the output would look like this:
     *
     * <pre>
     * Person@182f0db[
     *   name=John Doe
     *   age=33
     *   smoker=false
     * ]
     * </pre>
     */
    public static final ToStringStyle MULTI_LINE_STYLE = new MultiLineToStringStyle();

    /**
     * The no field names toString style. Using the
     * {@code Person} example from {@link ToStringBuilder}, the output
     * would look like this:
     *
     * <pre>
     * Person@182f0db[John Doe,33,false]
     * </pre>
     */
    public static final ToStringStyle NO_FIELD_NAMES_STYLE = new NoFieldNameToStringStyle();

    /**
     * The short prefix toString style. Using the {@code Person} example
     * from {@link ToStringBuilder}, the output would look like this:
     *
     * <pre>
     * Person[name=John Doe,age=33,smoker=false]
     * </pre>
     *
     * @since 2.1
     */
    public static final ToStringStyle SHORT_PREFIX_STYLE = new ShortPrefixToStringStyle();

    /**
     * The simple toString style. Using the {@code Person}
     * example from {@link ToStringBuilder}, the output would look like this:
     *
     * <pre>
     * John Doe,33,false
     * </pre>
     */
    public static final ToStringStyle SIMPLE_STYLE = new SimpleToStringStyle();

    /**
     * The no class name toString style. Using the {@code Person}
     * example from {@link ToStringBuilder}, the output would look like this:
     *
     * <pre>
     * [name=John Doe,age=33,smoker=false]
     * </pre>
     *
     * @since 3.4
     */
    public static final ToStringStyle NO_CLASS_NAME_STYLE = new NoClassNameToStringStyle();

    /**
     * The JSON toString style. Using the {@code Person} example from
     * {@link ToStringBuilder}, the output would look like this:
     *
     * <pre>
     * {"name": "John Doe", "age": 33, "smoker": true}
     * </pre>
     *
     * <strong>Note:</strong> Since field names are mandatory in JSON, this
     * ToStringStyle will throw an {@link UnsupportedOperationException} if no
     * field name is passed in while appending. Furthermore This ToStringStyle
     * will only generate valid JSON if referenced objects also produce JSON
     * when calling {@code toString()} on them.
     *
     * @since 3.4
     * @see <a href="http://json.org">json.org</a>
     */
    public static final ToStringStyle JSON_STYLE = new JsonToStringStyle();

    /**
     * <p>
     * A registry of objects used by {@code reflectionToString} methods
     * to detect cyclical object references and avoid infinite loops.
     * </p>
     */
    private static final ThreadLocal<WeakHashMap<Object, Object>> REGISTRY =
        new ThreadLocal<>();
    /*
     * Note that objects of this class are generally shared between threads, so
     * an instance variable would not be suitable here.
     *
     * In normal use the registry should always be left empty, because the caller
     * should call toString() which will clean up.
     *
     * See LANG-792
     */

    /**
     * <p>
     * Returns the registry of objects being traversed by the {@code reflectionToString}
     * methods in the current thread.
     * </p>
     *
     * @return Set the registry of objects being traversed
     */
    static Map<Object, Object> getRegistry() {
        return REGISTRY.get();
    }

    /**
     * <p>
     * Returns {@code true} if the registry contains the given object.
     * Used by the reflection methods to avoid infinite loops.
     * </p>
     *
     * @param value
     *                  The object to lookup in the registry.
     * @return boolean {@code true} if the registry contains the given
     *             object.
     */
    static boolean isRegistered(final Object value) {
        final Map<Object, Object> m = getRegistry();
        return m != null && m.containsKey(value);
    }

    /**
     * <p>
     * Registers the given object. Used by the reflection methods to avoid
     * infinite loops.
     * </p>
     *
     * @param value
     *                  The object to register.
     */
    static void register(final Object value) {
        if (value != null) {
            final Map<Object, Object> m = getRegistry();
            if (m == null) {
                REGISTRY.set(new WeakHashMap<>());
            }
            getRegistry().put(value, null);
        }
    }

    /**
     * <p>
     * Unregisters the given object.
     * </p>
     *
     * <p>
     * Used by the reflection methods to avoid infinite loops.
     * </p>
     *
     * @param value
     *                  The object to unregister.
     */
    static void unregister(final Object value) {
        if (value != null) {
            final Map<Object, Object> m = getRegistry();
            if (m != null) {
                m.remove(value);
                if (m.isEmpty()) {
                    REGISTRY.remove();
                }
            }
        }
    }

    /**
     * Whether to use the field names, the default is {@code true}.
     */
    private boolean useFieldNames = true;

    /**
     * Whether to use the class name, the default is {@code true}.
     */
    private boolean useClassName = true;

    /**
     * Whether to use short class names, the default is {@code false}.
     */
    private boolean useShortClassName;

    /**
     * Whether to use the identity hash code, the default is {@code true}.
     */
    private boolean useIdentityHashCode = true;

    /**
     * The content start {@code '['}.
     */
    private String contentStart = "[";

    /**
     * The content end {@code ']'}.
     */
    private String contentEnd = "]";

    /**
     * The field name value separator {@code '='}.
     */
    private String fieldNameValueSeparator = "=";

    /**
     * Whether the field separator should be added before any other fields.
     */
    private boolean fieldSeparatorAtStart;

    /**
     * Whether the field separator should be added after any other fields.
     */
    private boolean fieldSeparatorAtEnd;

    /**
     * The field separator {@code ','}.
     */
    private String fieldSeparator = ",";

    /**
     * The array start <code>'{'</code>.
     */
    private String arrayStart = "{";

    /**
     * The array separator {@code ','}.
     */
    private String arraySeparator = ",";

    /**
     * The detail for array content.
     */
    private boolean arrayContentDetail = true;

    /**
     * The array end {@code '}'}.
     */
    private String arrayEnd = "}";

    /**
     * The value to use when fullDetail is {@code null},
     * the default value is {@code true}.
     */
    private boolean defaultFullDetail = true;

    /**
     * The {@code null} text {@code '&lt;null&gt;'}.
     */
    private String nullText = "<null>";

    /**
     * The summary size text start {@code '&lt;size'}.
     */
    private String sizeStartText = "<size=";

    /**
     * The summary size text start {@code '&gt;'}.
     */
    private String sizeEndText = ">";

    /**
     * The summary object text start {@code '&lt;'}.
     */
    private String summaryObjectStartText = "<";

    /**
     * The summary object text start {@code '&gt;'}.
     */
    private String summaryObjectEndText = ">";

    //----------------------------------------------------------------------------

    /**
     * <p>Constructor.</p>
     */
    protected ToStringStyle() {
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} the superclass toString.</p>
     * <p>NOTE: It assumes that the toString has been created from the same ToStringStyle. </p>
     *
     * <p>A {@code null} {@code superToString} is ignored.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param superToString  the {@code super.toString()}
     * @since 2.0
     */
    public void appendSuper(final StringBuffer buffer, final String superToString) {
        appendToString(buffer, superToString);
    }

    /**
     * <p>Append to the {@code toString} another toString.</p>
     * <p>NOTE: It assumes that the toString has been created from the same ToStringStyle. </p>
     *
     * <p>A {@code null} {@code toString} is ignored.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param toString  the additional {@code toString}
     * @since 2.0
     */
    public void appendToString(final StringBuffer buffer, final String toString) {
        if (toString != null) {
            final int pos1 = toString.indexOf(contentStart) + contentStart.length();
            final int pos2 = toString.lastIndexOf(contentEnd);
            if (pos1 != pos2 && pos1 >= 0 && pos2 >= 0) {
                if (fieldSeparatorAtStart) {
                    removeLastFieldSeparator(buffer);
                }
                buffer.append(toString, pos1, pos2);
                appendFieldSeparator(buffer);
            }
        }
    }

    /**
     * <p>Append to the {@code toString} the start of data indicator.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param object  the {@code Object} to build a {@code toString} for
     */
    public void appendStart(final StringBuffer buffer, final Object object) {
        if (object != null) {
            appendClassName(buffer, object);
            appendIdentityHashCode(buffer, object);
            appendContentStart(buffer);
            if (fieldSeparatorAtStart) {
                appendFieldSeparator(buffer);
            }
        }
    }

    /**
     * <p>Append to the {@code toString} the end of data indicator.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param object  the {@code Object} to build a
     *  {@code toString} for.
     */
    public void appendEnd(final StringBuffer buffer, final Object object) {
        if (!this.fieldSeparatorAtEnd) {
            removeLastFieldSeparator(buffer);
        }
        appendContentEnd(buffer);
        unregister(object);
    }

    /**
     * <p>Remove the last field separator from the buffer.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @since 2.0
     */
    protected void removeLastFieldSeparator(final StringBuffer buffer) {
        if (StringUtils.endsWith(buffer, fieldSeparator)) {
            buffer.setLength(buffer.length() - fieldSeparator.length());
        }
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} an {@code Object}
     * value, printing the full {@code toString} of the
     * {@code Object} passed in.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param value  the value to add to the {@code toString}
     * @param fullDetail  {@code true} for detail, {@code false}
     *  for summary info, {@code null} for style decides
     */
    public void append(final StringBuffer buffer, final String fieldName, final Object value, final Boolean fullDetail) {
        appendFieldStart(buffer, fieldName);

        if (value == null) {
            appendNullText(buffer, fieldName);

        } else {
            appendInternal(buffer, fieldName, value, isFullDetail(fullDetail));
        }

        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} an {@code Object},
     * correctly interpreting its type.</p>
     *
     * <p>This method performs the main lookup by Class type to correctly
     * route arrays, {@code Collections}, {@code Maps} and
     * {@code Objects} to the appropriate method.</p>
     *
     * <p>Either detail or summary views can be specified.</p>
     *
     * <p>If a cycle is detected, an object will be appended with the
     * {@code Object.toString()} format.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString},
     *  not {@code null}
     * @param detail  output detail or not
     */
    protected void appendInternal(final StringBuffer buffer, final String fieldName, final Object value, final boolean detail) {
        if (isRegistered(value)
            && !(value instanceof Number || value instanceof Boolean || value instanceof Character)) {
           appendCyclicObject(buffer, fieldName, value);
           return;
        }

        register(value);

        try {
            if (value instanceof Collection<?>) {
                if (detail) {
                    appendDetail(buffer, fieldName, (Collection<?>) value);
                } else {
                    appendSummarySize(buffer, fieldName, ((Collection<?>) value).size());
                }

            } else if (value instanceof Map<?, ?>) {
                if (detail) {
                    appendDetail(buffer, fieldName, (Map<?, ?>) value);
                } else {
                    appendSummarySize(buffer, fieldName, ((Map<?, ?>) value).size());
                }

            } else if (value instanceof long[]) {
                if (detail) {
                    appendDetail(buffer, fieldName, (long[]) value);
                } else {
                    appendSummary(buffer, fieldName, (long[]) value);
                }

            } else if (value instanceof int[]) {
                if (detail) {
                    appendDetail(buffer, fieldName, (int[]) value);
                } else {
                    appendSummary(buffer, fieldName, (int[]) value);
                }

            } else if (value instanceof short[]) {
                if (detail) {
                    appendDetail(buffer, fieldName, (short[]) value);
                } else {
                    appendSummary(buffer, fieldName, (short[]) value);
                }

            } else if (value instanceof byte[]) {
                if (detail) {
                    appendDetail(buffer, fieldName, (byte[]) value);
                } else {
                    appendSummary(buffer, fieldName, (byte[]) value);
                }

            } else if (value instanceof char[]) {
                if (detail) {
                    appendDetail(buffer, fieldName, (char[]) value);
                } else {
                    appendSummary(buffer, fieldName, (char[]) value);
                }

            } else if (value instanceof double[]) {
                if (detail) {
                    appendDetail(buffer, fieldName, (double[]) value);
                } else {
                    appendSummary(buffer, fieldName, (double[]) value);
                }

            } else if (value instanceof float[]) {
                if (detail) {
                    appendDetail(buffer, fieldName, (float[]) value);
                } else {
                    appendSummary(buffer, fieldName, (float[]) value);
                }

            } else if (value instanceof boolean[]) {
                if (detail) {
                    appendDetail(buffer, fieldName, (boolean[]) value);
                } else {
                    appendSummary(buffer, fieldName, (boolean[]) value);
                }

            } else if (value.getClass().isArray()) {
                if (detail) {
                    appendDetail(buffer, fieldName, (Object[]) value);
                } else {
                    appendSummary(buffer, fieldName, (Object[]) value);
                }

            } else if (detail) {
                appendDetail(buffer, fieldName, value);
            } else {
                appendSummary(buffer, fieldName, value);
            }
        } finally {
            unregister(value);
        }
    }

    /**
     * <p>Append to the {@code toString} an {@code Object}
     * value that has been detected to participate in a cycle. This
     * implementation will print the standard string value of the value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString},
     *  not {@code null}
     *
     * @since 2.2
     */
    protected void appendCyclicObject(final StringBuffer buffer, final String fieldName, final Object value) {
       ObjectUtils.identityToString(buffer, value);
    }

    /**
     * <p>Append to the {@code toString} an {@code Object}
     * value, printing the full detail of the {@code Object}.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final Object value) {
        buffer.append(value);
    }

    /**
     * <p>Append to the {@code toString} a {@code Collection}.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param coll  the {@code Collection} to add to the
     *  {@code toString}, not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final Collection<?> coll) {
        buffer.append(coll);
    }

    /**
     * <p>Append to the {@code toString} a {@code Map}.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param map  the {@code Map} to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final Map<?, ?> map) {
        buffer.append(map);
    }

    /**
     * <p>Append to the {@code toString} an {@code Object}
     * value, printing a summary of the {@code Object}.</P>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendSummary(final StringBuffer buffer, final String fieldName, final Object value) {
        buffer.append(summaryObjectStartText);
        buffer.append(getShortClassName(value.getClass()));
        buffer.append(summaryObjectEndText);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code long}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param value  the value to add to the {@code toString}
     */
    public void append(final StringBuffer buffer, final String fieldName, final long value) {
        appendFieldStart(buffer, fieldName);
        appendDetail(buffer, fieldName, value);
        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} a {@code long}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final long value) {
        buffer.append(value);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} an {@code int}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param value  the value to add to the {@code toString}
     */
    public void append(final StringBuffer buffer, final String fieldName, final int value) {
        appendFieldStart(buffer, fieldName);
        appendDetail(buffer, fieldName, value);
        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} an {@code int}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final int value) {
        buffer.append(value);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code short}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param value  the value to add to the {@code toString}
     */
    public void append(final StringBuffer buffer, final String fieldName, final short value) {
        appendFieldStart(buffer, fieldName);
        appendDetail(buffer, fieldName, value);
        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} a {@code short}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final short value) {
        buffer.append(value);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code byte}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param value  the value to add to the {@code toString}
     */
    public void append(final StringBuffer buffer, final String fieldName, final byte value) {
        appendFieldStart(buffer, fieldName);
        appendDetail(buffer, fieldName, value);
        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} a {@code byte}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final byte value) {
        buffer.append(value);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code char}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param value  the value to add to the {@code toString}
     */
    public void append(final StringBuffer buffer, final String fieldName, final char value) {
        appendFieldStart(buffer, fieldName);
        appendDetail(buffer, fieldName, value);
        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} a {@code char}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final char value) {
        buffer.append(value);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code double}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param value  the value to add to the {@code toString}
     */
    public void append(final StringBuffer buffer, final String fieldName, final double value) {
        appendFieldStart(buffer, fieldName);
        appendDetail(buffer, fieldName, value);
        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} a {@code double}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final double value) {
        buffer.append(value);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code float}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param value  the value to add to the {@code toString}
     */
    public void append(final StringBuffer buffer, final String fieldName, final float value) {
        appendFieldStart(buffer, fieldName);
        appendDetail(buffer, fieldName, value);
        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} a {@code float}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final float value) {
        buffer.append(value);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code boolean}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param value  the value to add to the {@code toString}
     */
    public void append(final StringBuffer buffer, final String fieldName, final boolean value) {
        appendFieldStart(buffer, fieldName);
        appendDetail(buffer, fieldName, value);
        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} a {@code boolean}
     * value.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param value  the value to add to the {@code toString}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final boolean value) {
        buffer.append(value);
    }

    /**
     * <p>Append to the {@code toString} an {@code Object}
     * array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param array  the array to add to the toString
     * @param fullDetail  {@code true} for detail, {@code false}
     *  for summary info, {@code null} for style decides
     */
    public void append(final StringBuffer buffer, final String fieldName, final Object[] array, final Boolean fullDetail) {
        appendFieldStart(buffer, fieldName);

        if (array == null) {
            appendNullText(buffer, fieldName);

        } else if (isFullDetail(fullDetail)) {
            appendDetail(buffer, fieldName, array);

        } else {
            appendSummary(buffer, fieldName, array);
        }

        appendFieldEnd(buffer, fieldName);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} the detail of an
     * {@code Object} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final Object[] array) {
        buffer.append(arrayStart);
        for (int i = 0; i < array.length; i++) {
            final Object item = array[i];
            appendDetail(buffer, fieldName, i, item);
        }
        buffer.append(arrayEnd);
    }

    /**
     * <p>Append to the {@code toString} the detail of an
     * {@code Object} array item.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param i the array item index to add
     * @param item the array item to add
     * @since 3.11
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final int i, final Object item) {
        if (i > 0) {
            buffer.append(arraySeparator);
        }
        if (item == null) {
            appendNullText(buffer, fieldName);
        } else {
            appendInternal(buffer, fieldName, item, arrayContentDetail);
        }
    }

    /**
     * <p>Append to the {@code toString} the detail of an array type.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     * @since 2.0
     */
    protected void reflectionAppendArrayDetail(final StringBuffer buffer, final String fieldName, final Object array) {
        buffer.append(arrayStart);
        final int length = Array.getLength(array);
        for (int i = 0; i < length; i++) {
            final Object item = Array.get(array, i);
            appendDetail(buffer, fieldName, i, item);
        }
        buffer.append(arrayEnd);
    }

    /**
     * <p>Append to the {@code toString} a summary of an
     * {@code Object} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendSummary(final StringBuffer buffer, final String fieldName, final Object[] array) {
        appendSummarySize(buffer, fieldName, array.length);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code long}
     * array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param array  the array to add to the {@code toString}
     * @param fullDetail  {@code true} for detail, {@code false}
     *  for summary info, {@code null} for style decides
     */
    public void append(final StringBuffer buffer, final String fieldName, final long[] array, final Boolean fullDetail) {
        appendFieldStart(buffer, fieldName);

        if (array == null) {
            appendNullText(buffer, fieldName);

        } else if (isFullDetail(fullDetail)) {
            appendDetail(buffer, fieldName, array);

        } else {
            appendSummary(buffer, fieldName, array);
        }

        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} the detail of a
     * {@code long} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final long[] array) {
        buffer.append(arrayStart);
        for (int i = 0; i < array.length; i++) {
            if (i > 0) {
                buffer.append(arraySeparator);
            }
            appendDetail(buffer, fieldName, array[i]);
        }
        buffer.append(arrayEnd);
    }

    /**
     * <p>Append to the {@code toString} a summary of a
     * {@code long} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendSummary(final StringBuffer buffer, final String fieldName, final long[] array) {
        appendSummarySize(buffer, fieldName, array.length);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} an {@code int}
     * array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param array  the array to add to the {@code toString}
     * @param fullDetail  {@code true} for detail, {@code false}
     *  for summary info, {@code null} for style decides
     */
    public void append(final StringBuffer buffer, final String fieldName, final int[] array, final Boolean fullDetail) {
        appendFieldStart(buffer, fieldName);

        if (array == null) {
            appendNullText(buffer, fieldName);

        } else if (isFullDetail(fullDetail)) {
            appendDetail(buffer, fieldName, array);

        } else {
            appendSummary(buffer, fieldName, array);
        }

        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} the detail of an
     * {@code int} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final int[] array) {
        buffer.append(arrayStart);
        for (int i = 0; i < array.length; i++) {
            if (i > 0) {
                buffer.append(arraySeparator);
            }
            appendDetail(buffer, fieldName, array[i]);
        }
        buffer.append(arrayEnd);
    }

    /**
     * <p>Append to the {@code toString} a summary of an
     * {@code int} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendSummary(final StringBuffer buffer, final String fieldName, final int[] array) {
        appendSummarySize(buffer, fieldName, array.length);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code short}
     * array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param array  the array to add to the {@code toString}
     * @param fullDetail  {@code true} for detail, {@code false}
     *  for summary info, {@code null} for style decides
     */
    public void append(final StringBuffer buffer, final String fieldName, final short[] array, final Boolean fullDetail) {
        appendFieldStart(buffer, fieldName);

        if (array == null) {
            appendNullText(buffer, fieldName);

        } else if (isFullDetail(fullDetail)) {
            appendDetail(buffer, fieldName, array);

        } else {
            appendSummary(buffer, fieldName, array);
        }

        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} the detail of a
     * {@code short} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final short[] array) {
        buffer.append(arrayStart);
        for (int i = 0; i < array.length; i++) {
            if (i > 0) {
                buffer.append(arraySeparator);
            }
            appendDetail(buffer, fieldName, array[i]);
        }
        buffer.append(arrayEnd);
    }

    /**
     * <p>Append to the {@code toString} a summary of a
     * {@code short} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendSummary(final StringBuffer buffer, final String fieldName, final short[] array) {
        appendSummarySize(buffer, fieldName, array.length);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code byte}
     * array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param array  the array to add to the {@code toString}
     * @param fullDetail  {@code true} for detail, {@code false}
     *  for summary info, {@code null} for style decides
     */
    public void append(final StringBuffer buffer, final String fieldName, final byte[] array, final Boolean fullDetail) {
        appendFieldStart(buffer, fieldName);

        if (array == null) {
            appendNullText(buffer, fieldName);

        } else if (isFullDetail(fullDetail)) {
            appendDetail(buffer, fieldName, array);

        } else {
            appendSummary(buffer, fieldName, array);
        }

        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} the detail of a
     * {@code byte} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final byte[] array) {
        buffer.append(arrayStart);
        for (int i = 0; i < array.length; i++) {
            if (i > 0) {
                buffer.append(arraySeparator);
            }
            appendDetail(buffer, fieldName, array[i]);
        }
        buffer.append(arrayEnd);
    }

    /**
     * <p>Append to the {@code toString} a summary of a
     * {@code byte} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendSummary(final StringBuffer buffer, final String fieldName, final byte[] array) {
        appendSummarySize(buffer, fieldName, array.length);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code char}
     * array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param array  the array to add to the {@code toString}
     * @param fullDetail  {@code true} for detail, {@code false}
     *  for summary info, {@code null} for style decides
     */
    public void append(final StringBuffer buffer, final String fieldName, final char[] array, final Boolean fullDetail) {
        appendFieldStart(buffer, fieldName);

        if (array == null) {
            appendNullText(buffer, fieldName);

        } else if (isFullDetail(fullDetail)) {
            appendDetail(buffer, fieldName, array);

        } else {
            appendSummary(buffer, fieldName, array);
        }

        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} the detail of a
     * {@code char} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final char[] array) {
        buffer.append(arrayStart);
        for (int i = 0; i < array.length; i++) {
            if (i > 0) {
                buffer.append(arraySeparator);
            }
            appendDetail(buffer, fieldName, array[i]);
        }
        buffer.append(arrayEnd);
    }

    /**
     * <p>Append to the {@code toString} a summary of a
     * {@code char} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendSummary(final StringBuffer buffer, final String fieldName, final char[] array) {
        appendSummarySize(buffer, fieldName, array.length);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code double}
     * array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param array  the array to add to the toString
     * @param fullDetail  {@code true} for detail, {@code false}
     *  for summary info, {@code null} for style decides
     */
    public void append(final StringBuffer buffer, final String fieldName, final double[] array, final Boolean fullDetail) {
        appendFieldStart(buffer, fieldName);

        if (array == null) {
            appendNullText(buffer, fieldName);

        } else if (isFullDetail(fullDetail)) {
            appendDetail(buffer, fieldName, array);

        } else {
            appendSummary(buffer, fieldName, array);
        }

        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} the detail of a
     * {@code double} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final double[] array) {
        buffer.append(arrayStart);
        for (int i = 0; i < array.length; i++) {
            if (i > 0) {
                buffer.append(arraySeparator);
            }
            appendDetail(buffer, fieldName, array[i]);
        }
        buffer.append(arrayEnd);
    }

    /**
     * <p>Append to the {@code toString} a summary of a
     * {@code double} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendSummary(final StringBuffer buffer, final String fieldName, final double[] array) {
        appendSummarySize(buffer, fieldName, array.length);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code float}
     * array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param array  the array to add to the toString
     * @param fullDetail  {@code true} for detail, {@code false}
     *  for summary info, {@code null} for style decides
     */
    public void append(final StringBuffer buffer, final String fieldName, final float[] array, final Boolean fullDetail) {
        appendFieldStart(buffer, fieldName);

        if (array == null) {
            appendNullText(buffer, fieldName);

        } else if (isFullDetail(fullDetail)) {
            appendDetail(buffer, fieldName, array);

        } else {
            appendSummary(buffer, fieldName, array);
        }

        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} the detail of a
     * {@code float} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final float[] array) {
        buffer.append(arrayStart);
        for (int i = 0; i < array.length; i++) {
            if (i > 0) {
                buffer.append(arraySeparator);
            }
            appendDetail(buffer, fieldName, array[i]);
        }
        buffer.append(arrayEnd);
    }

    /**
     * <p>Append to the {@code toString} a summary of a
     * {@code float} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendSummary(final StringBuffer buffer, final String fieldName, final float[] array) {
        appendSummarySize(buffer, fieldName, array.length);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} a {@code boolean}
     * array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     * @param array  the array to add to the toString
     * @param fullDetail  {@code true} for detail, {@code false}
     *  for summary info, {@code null} for style decides
     */
    public void append(final StringBuffer buffer, final String fieldName, final boolean[] array, final Boolean fullDetail) {
        appendFieldStart(buffer, fieldName);

        if (array == null) {
            appendNullText(buffer, fieldName);

        } else if (isFullDetail(fullDetail)) {
            appendDetail(buffer, fieldName, array);

        } else {
            appendSummary(buffer, fieldName, array);
        }

        appendFieldEnd(buffer, fieldName);
    }

    /**
     * <p>Append to the {@code toString} the detail of a
     * {@code boolean} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendDetail(final StringBuffer buffer, final String fieldName, final boolean[] array) {
        buffer.append(arrayStart);
        for (int i = 0; i < array.length; i++) {
            if (i > 0) {
                buffer.append(arraySeparator);
            }
            appendDetail(buffer, fieldName, array[i]);
        }
        buffer.append(arrayEnd);
    }

    /**
     * <p>Append to the {@code toString} a summary of a
     * {@code boolean} array.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param array  the array to add to the {@code toString},
     *  not {@code null}
     */
    protected void appendSummary(final StringBuffer buffer, final String fieldName, final boolean[] array) {
        appendSummarySize(buffer, fieldName, array.length);
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Append to the {@code toString} the class name.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param object  the {@code Object} whose name to output
     */
    protected void appendClassName(final StringBuffer buffer, final Object object) {
        if (useClassName && object != null) {
            register(object);
            if (useShortClassName) {
                buffer.append(getShortClassName(object.getClass()));
            } else {
                buffer.append(object.getClass().getName());
            }
        }
    }

    /**
     * <p>Append the {@link System#identityHashCode(java.lang.Object)}.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param object  the {@code Object} whose id to output
     */
    protected void appendIdentityHashCode(final StringBuffer buffer, final Object object) {
        if (this.isUseIdentityHashCode() && object!=null) {
            register(object);
            buffer.append('@');
            buffer.append(Integer.toHexString(System.identityHashCode(object)));
        }
    }

    /**
     * <p>Append to the {@code toString} the content start.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     */
    protected void appendContentStart(final StringBuffer buffer) {
        buffer.append(contentStart);
    }

    /**
     * <p>Append to the {@code toString} the content end.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     */
    protected void appendContentEnd(final StringBuffer buffer) {
        buffer.append(contentEnd);
    }

    /**
     * <p>Append to the {@code toString} an indicator for {@code null}.</p>
     *
     * <p>The default indicator is {@code '&lt;null&gt;'}.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     */
    protected void appendNullText(final StringBuffer buffer, final String fieldName) {
        buffer.append(nullText);
    }

    /**
     * <p>Append to the {@code toString} the field separator.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     */
    protected void appendFieldSeparator(final StringBuffer buffer) {
        buffer.append(fieldSeparator);
    }

    /**
     * <p>Append to the {@code toString} the field start.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name
     */
    protected void appendFieldStart(final StringBuffer buffer, final String fieldName) {
        if (useFieldNames && fieldName != null) {
            buffer.append(fieldName);
            buffer.append(fieldNameValueSeparator);
        }
    }

    /**
     * <p>Append to the {@code toString} the field end.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     */
    protected void appendFieldEnd(final StringBuffer buffer, final String fieldName) {
        appendFieldSeparator(buffer);
    }

    /**
     * <p>Append to the {@code toString} a size summary.</p>
     *
     * <p>The size summary is used to summarize the contents of
     * {@code Collections}, {@code Maps} and arrays.</p>
     *
     * <p>The output consists of a prefix, the passed in size
     * and a suffix.</p>
     *
     * <p>The default format is {@code '&lt;size=n&gt;'}.</p>
     *
     * @param buffer  the {@code StringBuffer} to populate
     * @param fieldName  the field name, typically not used as already appended
     * @param size  the size to append
     */
    protected void appendSummarySize(final StringBuffer buffer, final String fieldName, final int size) {
        buffer.append(sizeStartText);
        buffer.append(size);
        buffer.append(sizeEndText);
    }

    /**
     * <p>Is this field to be output in full detail.</p>
     *
     * <p>This method converts a detail request into a detail level.
     * The calling code may request full detail ({@code true}),
     * but a subclass might ignore that and always return
     * {@code false}. The calling code may pass in
     * {@code null} indicating that it doesn't care about
     * the detail level. In this case the default detail level is
     * used.</p>
     *
     * @param fullDetailRequest  the detail level requested
     * @return whether full detail is to be shown
     */
    protected boolean isFullDetail(final Boolean fullDetailRequest) {
        if (fullDetailRequest == null) {
            return defaultFullDetail;
        }
        return fullDetailRequest.booleanValue();
    }

    /**
     * <p>Gets the short class name for a class.</p>
     *
     * <p>The short class name is the classname excluding
     * the package name.</p>
     *
     * @param cls  the {@code Class} to get the short name of
     * @return the short name
     */
    protected String getShortClassName(final Class<?> cls) {
        return ClassUtils.getShortClassName(cls);
    }

    // Setters and getters for the customizable parts of the style
    // These methods are not expected to be overridden, except to make public
    // (They are not public so that immutable subclasses can be written)
    //---------------------------------------------------------------------

    /**
     * <p>Gets whether to use the class name.</p>
     *
     * @return the current useClassName flag
     */
    protected boolean isUseClassName() {
        return useClassName;
    }

    /**
     * <p>Sets whether to use the class name.</p>
     *
     * @param useClassName  the new useClassName flag
     */
    protected void setUseClassName(final boolean useClassName) {
        this.useClassName = useClassName;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets whether to output short or long class names.</p>
     *
     * @return the current useShortClassName flag
     * @since 2.0
     */
    protected boolean isUseShortClassName() {
        return useShortClassName;
    }

    /**
     * <p>Sets whether to output short or long class names.</p>
     *
     * @param useShortClassName  the new useShortClassName flag
     * @since 2.0
     */
    protected void setUseShortClassName(final boolean useShortClassName) {
        this.useShortClassName = useShortClassName;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets whether to use the identity hash code.</p>
     *
     * @return the current useIdentityHashCode flag
     */
    protected boolean isUseIdentityHashCode() {
        return useIdentityHashCode;
    }

    /**
     * <p>Sets whether to use the identity hash code.</p>
     *
     * @param useIdentityHashCode  the new useIdentityHashCode flag
     */
    protected void setUseIdentityHashCode(final boolean useIdentityHashCode) {
        this.useIdentityHashCode = useIdentityHashCode;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets whether to use the field names passed in.</p>
     *
     * @return the current useFieldNames flag
     */
    protected boolean isUseFieldNames() {
        return useFieldNames;
    }

    /**
     * <p>Sets whether to use the field names passed in.</p>
     *
     * @param useFieldNames  the new useFieldNames flag
     */
    protected void setUseFieldNames(final boolean useFieldNames) {
        this.useFieldNames = useFieldNames;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets whether to use full detail when the caller doesn't
     * specify.</p>
     *
     * @return the current defaultFullDetail flag
     */
    protected boolean isDefaultFullDetail() {
        return defaultFullDetail;
    }

    /**
     * <p>Sets whether to use full detail when the caller doesn't
     * specify.</p>
     *
     * @param defaultFullDetail  the new defaultFullDetail flag
     */
    protected void setDefaultFullDetail(final boolean defaultFullDetail) {
        this.defaultFullDetail = defaultFullDetail;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets whether to output array content detail.</p>
     *
     * @return the current array content detail setting
     */
    protected boolean isArrayContentDetail() {
        return arrayContentDetail;
    }

    /**
     * <p>Sets whether to output array content detail.</p>
     *
     * @param arrayContentDetail  the new arrayContentDetail flag
     */
    protected void setArrayContentDetail(final boolean arrayContentDetail) {
        this.arrayContentDetail = arrayContentDetail;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the array start text.</p>
     *
     * @return the current array start text
     */
    protected String getArrayStart() {
        return arrayStart;
    }

    /**
     * <p>Sets the array start text.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param arrayStart  the new array start text
     */
    protected void setArrayStart(String arrayStart) {
        if (arrayStart == null) {
            arrayStart = StringUtils.EMPTY;
        }
        this.arrayStart = arrayStart;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the array end text.</p>
     *
     * @return the current array end text
     */
    protected String getArrayEnd() {
        return arrayEnd;
    }

    /**
     * <p>Sets the array end text.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param arrayEnd  the new array end text
     */
    protected void setArrayEnd(String arrayEnd) {
        if (arrayEnd == null) {
            arrayEnd = StringUtils.EMPTY;
        }
        this.arrayEnd = arrayEnd;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the array separator text.</p>
     *
     * @return the current array separator text
     */
    protected String getArraySeparator() {
        return arraySeparator;
    }

    /**
     * <p>Sets the array separator text.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param arraySeparator  the new array separator text
     */
    protected void setArraySeparator(String arraySeparator) {
        if (arraySeparator == null) {
            arraySeparator = StringUtils.EMPTY;
        }
        this.arraySeparator = arraySeparator;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the content start text.</p>
     *
     * @return the current content start text
     */
    protected String getContentStart() {
        return contentStart;
    }

    /**
     * <p>Sets the content start text.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param contentStart  the new content start text
     */
    protected void setContentStart(String contentStart) {
        if (contentStart == null) {
            contentStart = StringUtils.EMPTY;
        }
        this.contentStart = contentStart;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the content end text.</p>
     *
     * @return the current content end text
     */
    protected String getContentEnd() {
        return contentEnd;
    }

    /**
     * <p>Sets the content end text.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param contentEnd  the new content end text
     */
    protected void setContentEnd(String contentEnd) {
        if (contentEnd == null) {
            contentEnd = StringUtils.EMPTY;
        }
        this.contentEnd = contentEnd;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the field name value separator text.</p>
     *
     * @return the current field name value separator text
     */
    protected String getFieldNameValueSeparator() {
        return fieldNameValueSeparator;
    }

    /**
     * <p>Sets the field name value separator text.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param fieldNameValueSeparator  the new field name value separator text
     */
    protected void setFieldNameValueSeparator(String fieldNameValueSeparator) {
        if (fieldNameValueSeparator == null) {
            fieldNameValueSeparator = StringUtils.EMPTY;
        }
        this.fieldNameValueSeparator = fieldNameValueSeparator;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the field separator text.</p>
     *
     * @return the current field separator text
     */
    protected String getFieldSeparator() {
        return fieldSeparator;
    }

    /**
     * <p>Sets the field separator text.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param fieldSeparator  the new field separator text
     */
    protected void setFieldSeparator(String fieldSeparator) {
        if (fieldSeparator == null) {
            fieldSeparator = StringUtils.EMPTY;
        }
        this.fieldSeparator = fieldSeparator;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets whether the field separator should be added at the start
     * of each buffer.</p>
     *
     * @return the fieldSeparatorAtStart flag
     * @since 2.0
     */
    protected boolean isFieldSeparatorAtStart() {
        return fieldSeparatorAtStart;
    }

    /**
     * <p>Sets whether the field separator should be added at the start
     * of each buffer.</p>
     *
     * @param fieldSeparatorAtStart  the fieldSeparatorAtStart flag
     * @since 2.0
     */
    protected void setFieldSeparatorAtStart(final boolean fieldSeparatorAtStart) {
        this.fieldSeparatorAtStart = fieldSeparatorAtStart;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets whether the field separator should be added at the end
     * of each buffer.</p>
     *
     * @return fieldSeparatorAtEnd flag
     * @since 2.0
     */
    protected boolean isFieldSeparatorAtEnd() {
        return fieldSeparatorAtEnd;
    }

    /**
     * <p>Sets whether the field separator should be added at the end
     * of each buffer.</p>
     *
     * @param fieldSeparatorAtEnd  the fieldSeparatorAtEnd flag
     * @since 2.0
     */
    protected void setFieldSeparatorAtEnd(final boolean fieldSeparatorAtEnd) {
        this.fieldSeparatorAtEnd = fieldSeparatorAtEnd;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the text to output when {@code null} found.</p>
     *
     * @return the current text to output when null found
     */
    protected String getNullText() {
        return nullText;
    }

    /**
     * <p>Sets the text to output when {@code null} found.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param nullText  the new text to output when null found
     */
    protected void setNullText(String nullText) {
        if (nullText == null) {
            nullText = StringUtils.EMPTY;
        }
        this.nullText = nullText;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the start text to output when a {@code Collection},
     * {@code Map} or array size is output.</p>
     *
     * <p>This is output before the size value.</p>
     *
     * @return the current start of size text
     */
    protected String getSizeStartText() {
        return sizeStartText;
    }

    /**
     * <p>Sets the start text to output when a {@code Collection},
     * {@code Map} or array size is output.</p>
     *
     * <p>This is output before the size value.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param sizeStartText  the new start of size text
     */
    protected void setSizeStartText(String sizeStartText) {
        if (sizeStartText == null) {
            sizeStartText = StringUtils.EMPTY;
        }
        this.sizeStartText = sizeStartText;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the end text to output when a {@code Collection},
     * {@code Map} or array size is output.</p>
     *
     * <p>This is output after the size value.</p>
     *
     * @return the current end of size text
     */
    protected String getSizeEndText() {
        return sizeEndText;
    }

    /**
     * <p>Sets the end text to output when a {@code Collection},
     * {@code Map} or array size is output.</p>
     *
     * <p>This is output after the size value.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param sizeEndText  the new end of size text
     */
    protected void setSizeEndText(String sizeEndText) {
        if (sizeEndText == null) {
            sizeEndText = StringUtils.EMPTY;
        }
        this.sizeEndText = sizeEndText;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the start text to output when an {@code Object} is
     * output in summary mode.</p>
     *
     * <p>This is output before the size value.</p>
     *
     * @return the current start of summary text
     */
    protected String getSummaryObjectStartText() {
        return summaryObjectStartText;
    }

    /**
     * <p>Sets the start text to output when an {@code Object} is
     * output in summary mode.</p>
     *
     * <p>This is output before the size value.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param summaryObjectStartText  the new start of summary text
     */
    protected void setSummaryObjectStartText(String summaryObjectStartText) {
        if (summaryObjectStartText == null) {
            summaryObjectStartText = StringUtils.EMPTY;
        }
        this.summaryObjectStartText = summaryObjectStartText;
    }

    //---------------------------------------------------------------------

    /**
     * <p>Gets the end text to output when an {@code Object} is
     * output in summary mode.</p>
     *
     * <p>This is output after the size value.</p>
     *
     * @return the current end of summary text
     */
    protected String getSummaryObjectEndText() {
        return summaryObjectEndText;
    }

    /**
     * <p>Sets the end text to output when an {@code Object} is
     * output in summary mode.</p>
     *
     * <p>This is output after the size value.</p>
     *
     * <p>{@code null} is accepted, but will be converted to
     * an empty String.</p>
     *
     * @param summaryObjectEndText  the new end of summary text
     */
    protected void setSummaryObjectEndText(String summaryObjectEndText) {
        if (summaryObjectEndText == null) {
            summaryObjectEndText = StringUtils.EMPTY;
        }
        this.summaryObjectEndText = summaryObjectEndText;
    }

    //----------------------------------------------------------------------------

    /**
     * <p>Default {@code ToStringStyle}.</p>
     *
     * <p>This is an inner class rather than using
     * {@code StandardToStringStyle} to ensure its immutability.</p>
     */
    private static final class DefaultToStringStyle extends ToStringStyle {

        /**
         * Required for serialization support.
         *
         * @see java.io.Serializable
         */
        private static final long serialVersionUID = 1L;

        /**
         * <p>Constructor.</p>
         *
         * <p>Use the static constant rather than instantiating.</p>
         */
        DefaultToStringStyle() {
        }

        /**
         * <p>Ensure {@code Singleton} after serialization.</p>
         *
         * @return the singleton
         */
        private Object readResolve() {
            return DEFAULT_STYLE;
        }

    }

    //----------------------------------------------------------------------------

    /**
     * <p>{@code ToStringStyle} that does not print out
     * the field names.</p>
     *
     * <p>This is an inner class rather than using
     * {@code StandardToStringStyle} to ensure its immutability.
     */
    private static final class NoFieldNameToStringStyle extends ToStringStyle {

        private static final long serialVersionUID = 1L;

        /**
         * <p>Constructor.</p>
         *
         * <p>Use the static constant rather than instantiating.</p>
         */
        NoFieldNameToStringStyle() {
            this.setUseFieldNames(false);
        }

        /**
         * <p>Ensure {@code Singleton} after serialization.</p>
         *
         * @return the singleton
         */
        private Object readResolve() {
            return NO_FIELD_NAMES_STYLE;
        }

    }

    //----------------------------------------------------------------------------

    /**
     * <p>{@code ToStringStyle} that prints out the short
     * class name and no identity hashcode.</p>
     *
     * <p>This is an inner class rather than using
     * {@code StandardToStringStyle} to ensure its immutability.</p>
     */
    private static final class ShortPrefixToStringStyle extends ToStringStyle {

        private static final long serialVersionUID = 1L;

        /**
         * <p>Constructor.</p>
         *
         * <p>Use the static constant rather than instantiating.</p>
         */
        ShortPrefixToStringStyle() {
            this.setUseShortClassName(true);
            this.setUseIdentityHashCode(false);
        }

        /**
         * <p>Ensure <code>Singleton</ode> after serialization.</p>
         * @return the singleton
         */
        private Object readResolve() {
            return SHORT_PREFIX_STYLE;
        }

    }

    //----------------------------------------------------------------------------

    /**
     * <p>{@code ToStringStyle} that does not print out the
     * classname, identity hashcode, content start or field name.</p>
     *
     * <p>This is an inner class rather than using
     * {@code StandardToStringStyle} to ensure its immutability.</p>
     */
    private static final class SimpleToStringStyle extends ToStringStyle {

        private static final long serialVersionUID = 1L;

        /**
         * <p>Constructor.</p>
         *
         * <p>Use the static constant rather than instantiating.</p>
         */
        SimpleToStringStyle() {
            this.setUseClassName(false);
            this.setUseIdentityHashCode(false);
            this.setUseFieldNames(false);
            this.setContentStart(StringUtils.EMPTY);
            this.setContentEnd(StringUtils.EMPTY);
        }

        /**
         * <p>Ensure <code>Singleton</ode> after serialization.</p>
         * @return the singleton
         */
        private Object readResolve() {
            return SIMPLE_STYLE;
        }

    }

    //----------------------------------------------------------------------------

    /**
     * <p>{@code ToStringStyle} that outputs on multiple lines.</p>
     *
     * <p>This is an inner class rather than using
     * {@code StandardToStringStyle} to ensure its immutability.</p>
     */
    private static final class MultiLineToStringStyle extends ToStringStyle {

        private static final long serialVersionUID = 1L;

        /**
         * <p>Constructor.</p>
         *
         * <p>Use the static constant rather than instantiating.</p>
         */
        MultiLineToStringStyle() {
            this.setContentStart("[");
            this.setFieldSeparator(System.lineSeparator() + "  ");
            this.setFieldSeparatorAtStart(true);
            this.setContentEnd(System.lineSeparator() + "]");
        }

        /**
         * <p>Ensure {@code Singleton} after serialization.</p>
         *
         * @return the singleton
         */
        private Object readResolve() {
            return MULTI_LINE_STYLE;
        }

    }

    //----------------------------------------------------------------------------

    /**
     * <p>{@code ToStringStyle} that does not print out the classname
     * and identity hash code but prints content start and field names.</p>
     *
     * <p>This is an inner class rather than using
     * {@code StandardToStringStyle} to ensure its immutability.</p>
     */
    private static final class NoClassNameToStringStyle extends ToStringStyle {

        private static final long serialVersionUID = 1L;

        /**
         * <p>Constructor.</p>
         *
         * <p>Use the static constant rather than instantiating.</p>
         */
        NoClassNameToStringStyle() {
            this.setUseClassName(false);
            this.setUseIdentityHashCode(false);
        }

        /**
         * <p>Ensure {@code Singleton} after serialization.</p>
         *
         * @return the singleton
         */
        private Object readResolve() {
            return NO_CLASS_NAME_STYLE;
        }

    }

    // ----------------------------------------------------------------------------

    /**
     * <p>
     * {@code ToStringStyle} that outputs with JSON format.
     * </p>
     *
     * <p>
     * This is an inner class rather than using
     * {@code StandardToStringStyle} to ensure its immutability.
     * </p>
     *
     * @since 3.4
     * @see <a href="http://json.org">json.org</a>
     */
    private static final class JsonToStringStyle extends ToStringStyle {

        private static final long serialVersionUID = 1L;

        private static final String FIELD_NAME_QUOTE = "\"";

        /**
         * <p>
         * Constructor.
         * </p>
         *
         * <p>
         * Use the static constant rather than instantiating.
         * </p>
         */
        JsonToStringStyle() {
            this.setUseClassName(false);
            this.setUseIdentityHashCode(false);

            this.setContentStart("{");
            this.setContentEnd("}");

            this.setArrayStart("[");
            this.setArrayEnd("]");

            this.setFieldSeparator(",");
            this.setFieldNameValueSeparator(":");

            this.setNullText("null");

            this.setSummaryObjectStartText("\"<");
            this.setSummaryObjectEndText(">\"");

            this.setSizeStartText("\"<size=");
            this.setSizeEndText(">\"");
        }

        @Override
        public void append(final StringBuffer buffer, final String fieldName,
                           final Object[] array, final Boolean fullDetail) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }
            if (!isFullDetail(fullDetail)) {
                throw new UnsupportedOperationException(
                        "FullDetail must be true when using JsonToStringStyle");
            }

            super.append(buffer, fieldName, array, fullDetail);
        }

        @Override
        public void append(final StringBuffer buffer, final String fieldName, final long[] array,
                           final Boolean fullDetail) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }
            if (!isFullDetail(fullDetail)) {
                throw new UnsupportedOperationException(
                        "FullDetail must be true when using JsonToStringStyle");
            }

            super.append(buffer, fieldName, array, fullDetail);
        }

        @Override
        public void append(final StringBuffer buffer, final String fieldName, final int[] array,
                           final Boolean fullDetail) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }
            if (!isFullDetail(fullDetail)) {
                throw new UnsupportedOperationException(
                        "FullDetail must be true when using JsonToStringStyle");
            }

            super.append(buffer, fieldName, array, fullDetail);
        }

        @Override
        public void append(final StringBuffer buffer, final String fieldName,
                           final short[] array, final Boolean fullDetail) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }
            if (!isFullDetail(fullDetail)) {
                throw new UnsupportedOperationException(
                        "FullDetail must be true when using JsonToStringStyle");
            }

            super.append(buffer, fieldName, array, fullDetail);
        }

        @Override
        public void append(final StringBuffer buffer, final String fieldName, final byte[] array,
                           final Boolean fullDetail) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }
            if (!isFullDetail(fullDetail)) {
                throw new UnsupportedOperationException(
                        "FullDetail must be true when using JsonToStringStyle");
            }

            super.append(buffer, fieldName, array, fullDetail);
        }

        @Override
        public void append(final StringBuffer buffer, final String fieldName, final char[] array,
                           final Boolean fullDetail) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }
            if (!isFullDetail(fullDetail)) {
                throw new UnsupportedOperationException(
                        "FullDetail must be true when using JsonToStringStyle");
            }

            super.append(buffer, fieldName, array, fullDetail);
        }

        @Override
        public void append(final StringBuffer buffer, final String fieldName,
                           final double[] array, final Boolean fullDetail) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }
            if (!isFullDetail(fullDetail)) {
                throw new UnsupportedOperationException(
                        "FullDetail must be true when using JsonToStringStyle");
            }

            super.append(buffer, fieldName, array, fullDetail);
        }

        @Override
        public void append(final StringBuffer buffer, final String fieldName,
                           final float[] array, final Boolean fullDetail) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }
            if (!isFullDetail(fullDetail)) {
                throw new UnsupportedOperationException(
                        "FullDetail must be true when using JsonToStringStyle");
            }

            super.append(buffer, fieldName, array, fullDetail);
        }

        @Override
        public void append(final StringBuffer buffer, final String fieldName,
                           final boolean[] array, final Boolean fullDetail) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }
            if (!isFullDetail(fullDetail)) {
                throw new UnsupportedOperationException(
                        "FullDetail must be true when using JsonToStringStyle");
            }

            super.append(buffer, fieldName, array, fullDetail);
        }

        @Override
        public void append(final StringBuffer buffer, final String fieldName, final Object value,
                           final Boolean fullDetail) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }
            if (!isFullDetail(fullDetail)) {
                throw new UnsupportedOperationException(
                        "FullDetail must be true when using JsonToStringStyle");
            }

            super.append(buffer, fieldName, value, fullDetail);
        }

        @Override
        protected void appendDetail(final StringBuffer buffer, final String fieldName, final char value) {
            appendValueAsString(buffer, String.valueOf(value));
        }

        @Override
        protected void appendDetail(final StringBuffer buffer, final String fieldName, final Object value) {

            if (value == null) {
                appendNullText(buffer, fieldName);
                return;
            }

            if (value instanceof String || value instanceof Character) {
                appendValueAsString(buffer, value.toString());
                return;
            }

            if (value instanceof Number || value instanceof Boolean) {
                buffer.append(value);
                return;
            }

            final String valueAsString = value.toString();
            if (isJsonObject(valueAsString) || isJsonArray(valueAsString)) {
                buffer.append(value);
                return;
            }

            appendDetail(buffer, fieldName, valueAsString);
        }

        @Override
        protected void appendDetail(final StringBuffer buffer, final String fieldName, final Collection<?> coll) {
            if (coll != null && !coll.isEmpty()) {
                buffer.append(getArrayStart());
                int i = 0;
                for (final Object item : coll) {
                    appendDetail(buffer, fieldName, i++, item);
                }
                buffer.append(getArrayEnd());
                return;
            }

            buffer.append(coll);
        }

        @Override
        protected void appendDetail(final StringBuffer buffer, final String fieldName, final Map<?, ?> map) {
            if (map != null && !map.isEmpty()) {
                buffer.append(getContentStart());

                boolean firstItem = true;
                for (final Entry<?, ?> entry : map.entrySet()) {
                    final String keyStr = Objects.toString(entry.getKey(), null);
                    if (keyStr != null) {
                        if (firstItem) {
                            firstItem = false;
                        } else {
                            appendFieldEnd(buffer, keyStr);
                        }
                        appendFieldStart(buffer, keyStr);
                        final Object value = entry.getValue();
                        if (value == null) {
                            appendNullText(buffer, keyStr);
                        } else {
                            appendInternal(buffer, keyStr, value, true);
                        }
                    }
                }

                buffer.append(getContentEnd());
                return;
            }

            buffer.append(map);
        }

        private boolean isJsonArray(final String valueAsString) {
            return valueAsString.startsWith(getArrayStart())
                    && valueAsString.endsWith(getArrayEnd());
        }

        private boolean isJsonObject(final String valueAsString) {
            return valueAsString.startsWith(getContentStart())
                    && valueAsString.endsWith(getContentEnd());
        }

        /**
         * Appends the given String enclosed in double-quotes to the given StringBuffer.
         *
         * @param buffer the StringBuffer to append the value to.
         * @param value the value to append.
         */
        private void appendValueAsString(final StringBuffer buffer, final String value) {
            buffer.append('"').append(StringEscapeUtils.escapeJson(value)).append('"');
        }

        @Override
        protected void appendFieldStart(final StringBuffer buffer, final String fieldName) {

            if (fieldName == null) {
                throw new UnsupportedOperationException(
                        "Field names are mandatory when using JsonToStringStyle");
            }

            super.appendFieldStart(buffer, FIELD_NAME_QUOTE + StringEscapeUtils.escapeJson(fieldName)
                    + FIELD_NAME_QUOTE);
        }

        /**
         * <p>
         * Ensure {@code Singleton} after serialization.
         * </p>
         *
         * @return the singleton
         */
        private Object readResolve() {
            return JSON_STYLE;
        }

    }
}
