/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/**
 * @file Driver.h
 *
 * @author Florian Corzilius
 * @since 2012-03-19
 * @version 2012-03-19
 */

#ifndef SMTTWO_DRIVER_H
#define SMTTWO_DRIVER_H

#include <string>
#include <vector>
#include <set>
#include <map>

/** The smtrat namespace is used to encapsulate the three parser classes
 * smtrat::Parser, smtrat::Scanner and smtrat::Driver */
namespace smtrat
{
    // forward declaration
    class Formula;

    /** The driver class brings together all components. It creates an instance of
     * the parser and scanner classes and connects them. Then the input stream is
     * fed into the scanner object and the parser gets it's token
     * sequence. Furthermore the driver object is available in the grammar rules as
     * a parameter. Therefore the driver class contains a reference to the
     * structure into which the parsed data is saved. */
    class Driver
    {
        public:
            /// construct a new parser driver context
            Driver( class Formula * );

            ~Driver();

            /// enable debug output in the flex scanner
            bool trace_scanning;

            /// enable debug output in the bison parser
            bool trace_parsing;

            /// stream name (file or input stream) used for error messages.
            std::string streamname;

            /** Invoke the scanner and parser for a stream.
             * @param in    input stream
             * @param sname stream name for error messages
             * @return      true if successfully parsed
             */
            bool parse_stream( std::istream& in, const std::string& sname = "stream input" );

            /** Invoke the scanner and parser on an input string.
             * @param input input string
             * @param sname stream name for error messages
             * @return      true if successfully parsed
             */
            bool parse_string( const std::string& input, const std::string& sname = "string stream" );

            /** Invoke the scanner and parser on a file. Use parse_stream with a
             * std::ifstream if detection of file reading errors is required.
             * @param filename  input file name
             * @return      true if successfully parsed
             */
            bool parse_file( const std::string& filename );

            // To demonstrate pure handling of parse errors, instead of
            // simply dumping them on the standard error output, we will pass
            // them to the driver using the following two member functions.

            /** Error handling with associated line number. This can be modified to
             * output the error e.g. to a dialog box. */
            void error( const class location &l, const std::string& m );

            /** General error handling. This can be modified to output the error
             * e.g. to a dialog box. */
            void error( const std::string& m );

            static std::string replace( const std::string, const std::string, const std::string );

            /** Pointer to the current lexer instance, this is used to connect the
             * parser to the scanner. It is used in the yylex macro. */
            class Scanner *lexer;

            /** Reference to the calculator context filled during parsing of the
             * expressions. */
            class Formula *formulaRoot;

            std::set<std::string>              collectedBooleans;

            std::map<std::string, std::string> collectedRealAuxilliaries;

            int status;

            std::map< const std::string, const std::string > realsymbolpartsToReplace;

            std::map< const std::string, class Formula*> collectedBooleanAuxilliaries;
    };

}    // namespace smtrat

#endif // SMTTWO_DRIVER_H