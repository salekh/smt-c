/* SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * Class to create a decision tuple object.
 * @author Florian Corzilius
 * @since 2010-05-11
 * @version 2011-12-05
 */

#ifndef SMTRAT_VS_STATE_H
#define SMTRAT_VS_STATE_H

#include <map>
#include <limits.h>
#include "Substitution.h"
#include "Tools.h"

namespace vs
{

/*
 * Type and object definitions:
 */
enum StateType{ TEST_CANDIDATE_TO_GENERATE,
				SUBSTITUTION_TO_APPLY	  ,
				COMBINE_SUBRESULTS		   };

/*
 * A unsigned integer is between 0 and 4.294.967.295, so there are 4.294 different valuations.
 * The remaining 6 digits are to make a valuation unique, so there are 967.295 different IDs.
 */
const unsigned VALUATION_FACTOR				= 1000000	;
const unsigned MAX_CONSTRAINT_VALUATION 	= 10		;
const unsigned MIN_VALUATION				= 0			;
const unsigned MAX_VALUATION				= UINT_MAX	;
const unsigned MAX_ID	  	        		= UINT_MAX	;
const signed   MAX_SOLVABLE_DEGREE 			= 2			;
const unsigned MAXIMUM_VARIABLE_VALUATION 	= 10000000	;

template <class elementType> struct setOfPointerComp
{
	bool operator() ( const std::set< elementType > set1,
					  const std::set< elementType > set2 )
	{
		class std::set< elementType >::const_iterator elem1 = set1.begin();
		class std::set< elementType >::const_iterator elem2 = set2.begin();
		while( elem1!=set1.end() && elem2!=set2.end() )
		{
			if( set1.key_comp()( *elem2, *elem1 ) )
			{
				return false;
			}
			else if( set1.key_comp()( *elem1, *elem2 ) )
			{
				return true;
			}
			else
			{
				elem1++;
				elem2++;
			}
		}
		if( elem2!=set2.end() )
		{
			return true;
		}
		else
		{
			return false;
		}
	}
};

struct setOfCondPointerComp
{
	bool operator() ( const ConditionSet set1,
					  const ConditionSet set2 )
	{
		ConditionSet::const_iterator cond1 = set1.begin();
		ConditionSet::const_iterator cond2 = set2.begin();
		while( cond1!=set1.end() && cond2!=set2.end() )
		{
			if( set1.key_comp()( *cond2, *cond1 ) )
			{
				return false;
			}
			else if( set1.key_comp()( *cond1, *cond2 ) )
			{
				return true;
			}
			else
			{
				cond1++;
				cond2++;
			}
		}
		if( cond2!=set2.end() )
		{
			return true;
		}
		else
		{
			return false;
		}
	}
};

typedef std::set< ConditionSet, setOfCondPointerComp >	ConditionSetSet	;

struct setOfSetsOfCondPointerComp
{
	bool operator() ( const ConditionSetSet setOfSet1,
					  const ConditionSetSet setOfSet2 )
	{
		ConditionSetSet::const_iterator set1 = setOfSet1.begin();
		ConditionSetSet::const_iterator set2 = setOfSet2.begin();
		while( set1!=setOfSet1.end() && set2!=setOfSet2.end() )
		{
			if( setOfSet1.key_comp()( *set2, *set1 ) )
			{
				return false;
			}
			else if( setOfSet1.key_comp()( *set1, *set2 ) )
			{
				return true;
			}
			else
			{
				set1++;
				set2++;
			}
		}
		if( set2!=setOfSet2.end() )
		{
			return true;
		}
		else
		{
			return false;
		}
	}
};

typedef std::set< ConditionSetSet, setOfSetsOfCondPointerComp > ConditionSetSetSet;

struct unsignedGreater
{
	bool operator()
	( const unsigned& lhs, const unsigned& rhs ) const
	{
		return lhs>rhs;
	}
};

struct subComp
{
	bool operator()
	(
		const Substitution* const pSubA,
		const Substitution* const pSubB
	) const
	{
		if( pSubA==NULL && pSubB==NULL )
		{
			return false;
		}
		else if( pSubA==NULL )
		{
			return true;
		}
		else if( pSubB==NULL )
		{
			return false;
		}
		else
		{
			return (*pSubA)<(*pSubB);
		}
	}
};

typedef std::vector	< Condition* > 			ConditionVector						;
typedef std::vector	< ConditionVector > 	DisjunctionOfConditionConjunctions	;
typedef std::vector	< smtrat::Constraint* > TS_ConstraintConjunction			;


class State
{
public:

	/**
	 * Constructors:
	 */
	State	( );
	State	( State* const		 ,
			  const Substitution& );

	/**
	 * Destructor:
	 */
	~State	( )	;

	/*
	 * Intern type structur:
	 */
	typedef std::map	< const Substitution* const, ConditionSetSetSet, subComp > 	ConflictSets		 ;
	typedef std::vector	< State* >													StateVector			 ;
	typedef std::vector < std::pair< ConditionVector, bool > > 						SubstitutionResult	 ;
	typedef std::vector < SubstitutionResult > 										SubstitutionResults	 ;
	typedef std::vector < std::pair< unsigned, unsigned  > >						SubResultCombination;

	/**
	 * Methods:
	 */

	const bool&					isRoot		        		( ) const 	{ return mRoot	   					 									; }
	const bool&					toHighDegree        		( ) const 	{ return mToHighDegree				 									; }
	bool&						rToHighDegree        		( ) 		{ return mToHighDegree				 									; }
#ifndef VS_USE_REDLOG
	const bool&					markedAsDeleted        		( ) const 	{ return mMarkedAsDeleted			 									; }
	bool&						rMarkedAsDeleted        	( ) 	 	{ return mMarkedAsDeleted			 									; }
#endif
	const bool&					hasChildrenToInsert    		( ) const 	{ return mHasChildrenToInsert		 									; }
	bool&						rHasChildrenToInsert       	( ) 	 	{ return mHasChildrenToInsert		 									; }
	const std::string& 			index		        		( ) const 	{ return *mpIndex	   				 									; }
	unsigned&					rValuation	        		( )       	{ return mValuation	   				 									; }
	const unsigned&				valuation	        		( ) const 	{ return mValuation	   				 									; }
	const unsigned&				id	        				( ) const 	{ return mID	   					 									; }
	StateVector&				rChildren	        		( )       	{ return *mpChildren	   			 									; }
	const StateVector& 			children 	        		( ) const 	{ return *mpChildren	   			 									; }
	State* const				pFather						( ) const  	{ return mpFather	   				 									; }
	const State& 				father						( ) const  	{ return *mpFather	   				 									; }
	State&  					rFather						( )       	{ return *mpFather	   				 									; }
	ConflictSets&				rConflictSets 				( )       	{ return *mpConflictSets			 									; }
	const ConflictSets& 		conflictSets				( ) const 	{ return *mpConflictSets			 									; }
	bool&						rHasRecentlyAddedConditions ( )  		{ return mHasRecentlyAddedConditions 									; }
	const bool					hasRecentlyAddedConditions  ( ) const 	{ return mHasRecentlyAddedConditions 									; }
	bool&						rInconsistent				( ) 	 	{ return mInconsistent				 									; }
	const bool					isInconsistent				( ) const 	{ return mInconsistent				 									; }
	ConditionVector&			rConditions	        		( )       	{ return *mpConditions	   			 									; }
	const ConditionVector&		conditions	      			( ) const 	{ return *mpConditions	   			 									; }
	Substitution&				rSubstitution				( )       	{ return *mpSubstitution 			 									; }
	const Substitution&			substitution 				( ) const 	{ return *mpSubstitution 			 									; }
	SubstitutionResults&		rSubstitutionResults		( )       	{ return *mpSubstitutionResults		 									; }
	const SubstitutionResults&	substitutionResults			( ) const 	{ return *mpSubstitutionResults		 									; }
	SubResultCombination&		rSubResultCombination		( )       	{ return *mpSubResultCombination	 									; }
	const SubResultCombination&	subResultCombination		( ) const 	{ return *mpSubResultCombination	 									; }
	const Substitution* const	pSubstitution 				( ) const 	{ return mpSubstitution 			 									; }
	const bool					conditionsSimplified		( ) const	{ return mConditionsSimplified		 									; }
	const bool					subResultsSimplified		( ) const	{ return mSubResultsSimplified		 									; }
	bool&						rSubResultsSimplified		( ) 		{ return mSubResultsSimplified		 									; }
	const bool					takeSubResultCombAgain		( ) const	{ return mTakeSubResultCombAgain	 									; }
	bool&						rTakeSubResultCombAgain		( ) 		{ return mTakeSubResultCombAgain	 									; }
	const bool					tryToRefreshIndex			( ) const	{ return mTryToRefreshIndex			 									; }
	const bool					hasSubResultsCombination	( ) const	{ return mpSubResultCombination!=NULL									; }
	const bool					hasSubstitutionResults		( ) const	{ return mpSubstitutionResults!=NULL 									; }
	const bool					unfinished					( ) const	{ return (mpSubstitutionResults->size()>mpSubResultCombination->size())	; }
	const StateType				stateType					( ) const	{ return mStateType														; }
	StateType&					rStateType					( ) 		{ return mStateType														; }
	Condition*		 			pOriginalCondition			( )	const 	{ return mpOriginalCondition											; }
	const Condition& 			originalCondition			( )	const 	{ return *mpOriginalCondition											; }

	void						setOriginalCondition		( Condition* const _pOCondition ) 	{ mpOriginalCondition=_pOCondition; }

	// Data access methods (read only).
	const unsigned 							treeDepth							( ) 														const	;
	bool									substitutionApplicable  			( )				        									const	;
	bool									substitutionApplicable  			( const smtrat::Constraint& )								const	;
	bool									hasNoninvolvedCondition 			( )															const	;
	bool									hasChildWithID 						( )															const	;
	bool									occursInEquation					( const std::string& )										const   ;
	bool									hasFurtherUncheckedTestCandidates 	( )															const	;
	void 									variables							( std::set< std::string >& )								const	;
	unsigned 								numberOfNodes						( ) 														const	;
	const std::pair< unsigned, unsigned > 	valuationPlusID						( ) 														const 	;
	bool 									checkSubResultsCombs				( ) 														const	;

	// Data access methods (read and write).
	State&									root								( )																	;
	bool									unfinishedAncestor					( State*& )															;
	bool 									bestCondition						( Condition*&,
																				  unsigned 		 )													;
	ConditionVector::iterator 				constraintExists 					( const smtrat::Constraint& )										;

	// Manipulating methods.
	void 									simplify							( )																	;
	bool 									simplify							( ConditionVector&,
																				  ConditionVector&,
																				  ConditionSetSet& )												;
	void									setIndex							( const std::string& )  											;
	bool									setID								( const unsigned )  												;
	void 									addConflictSet						( const Substitution* const,
																				  ConditionSetSet&		   )										;
	void 									addConflicts						( const Substitution* const,
																				  ConditionSetSet&		   )										;
	bool									updateOCondsOfSubstitutions 		( const Substitution& )												;
	void 									addSubstitutionResults				( std::vector< DisjunctionOfConditionConjunctions >& )				;
	bool 									extendSubResultCombination			( )																	;
	bool 									nextSubResultCombination			( )																	;
	const ConditionVector					getCurrentSubresultCombination		( ) 														const	;
	bool 									refreshConditions					( )																	;
	void									initConditionFlags					( )																	;
	bool 									initIndex							( const GiNaC::symtab& )											;
	void									addCondition						( const smtrat::Constraint&	   ,
																  				  const ConditionSet&   ,
																				  const unsigned 		   ,
																				  const bool 				)										;
	void									deleteConditions					( ConditionVector& )												;
	bool									addChild							( const std::string& 	   ,
																				  const Substitution_Type& ,
																				  const ConditionSet&	)										;
	bool									addChild							( const GiNaC::ex& 			,
																				  const smtrat::Constraint_Relation&,
																	 			  const GiNaC::symtab&		,
																				  const std::string& 		,
																				  const GiNaC::ex&			,
																				  const GiNaC::ex&			,
																				  const GiNaC::ex&			,
																				  const GiNaC::ex&			,
																				  const Substitution_Type& 	,
																				  const ConditionSet&	 )										;
	bool									addChild							( const GiNaC::ex& 			,
																				  const smtrat::Constraint_Relation&,
																				  const GiNaC::ex& 			,
																				  const smtrat::Constraint_Relation&,
																 				  const GiNaC::symtab&		,
																				  const std::string& 		,
																				  const GiNaC::ex&			,
																				  const GiNaC::ex&			,
																				  const GiNaC::ex&			,
																				  const GiNaC::ex&			,
																				  const Substitution_Type& 	,
																				  const ConditionSet&	 )										;
	void									updateValuation						( )	      			       											;
	bool									passConflictToFather				( )																	;

	// Printing methods.
	void 									print								( const std::string = "***",
																				  std::ostream&	= std::cout	)								  const	;
	void 									printAlone							( const std::string = "***",
								 	  											  std::ostream&	= std::cout	)								  const	;
	void 									printConditions						( const std::string = "***",
								 	  											  std::ostream&	= std::cout	)								  const	;
	void 									printSubstitutionResults			( const std::string = "***",
								 	  											  std::ostream&	= std::cout	)								  const	;
	void 									printSubstitutionResultCombination	( const std::string = "***",
								 	  											  std::ostream&	= std::cout	)								  const	;
	void 									printSubstitutionResultCombinationAsNumbers	( const std::string = "***",
								 	  											  		  std::ostream& = std::cout )						  const	;
	void 									printConflictSets					( const std::string = "***",
								 	  											  std::ostream&	= std::cout	)								  const	;
	// Static methods.
	static unsigned 						coveringSet							( const ConditionSetSetSet&,
																		 		  ConditionSet&			  ,
																		 		  const unsigned		 	   ) 									;

private:

	/**
	 * Attributes:
	 */
	bool			    	mRoot						;
	bool					mHasRecentlyAddedConditions	;
	bool					mInconsistent				;
	bool					mToHighDegree				;
	bool					mMarkedAsDeleted			;
	bool					mHasChildrenToInsert		;
	bool					mConditionsSimplified		;
	bool					mSubResultsSimplified		;
	bool					mTakeSubResultCombAgain		;
	bool					mTryToRefreshIndex			;
	unsigned		    	mValuation					;
	unsigned		    	mID							;
	StateType				mStateType					;
	std::string*			mpIndex						;
	Condition*				mpOriginalCondition			;
	ConditionVector* 		mpConditions				;
	StateVector* 			mpChildren					;
	State*					mpFather					;
	ConflictSets*			mpConflictSets				;
	Substitution*			mpSubstitution				;
	SubstitutionResults* 	mpSubstitutionResults		;
	SubResultCombination*	mpSubResultCombination		;
};

typedef std::map	< const Substitution* const, ConditionSetSetSet, subComp > 	ConflictSets		;
typedef std::vector	< State* >													StateVector			;
typedef std::vector < std::pair< ConditionVector, bool > > 						SubstitutionResult	;
typedef std::vector	< SubstitutionResult > 										SubstitutionResults	;
typedef std::vector < std::pair< unsigned, unsigned  > >						SubResultCombination;

} // end namspace vs

#endif

