/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "isop.hpp"
#include "print.hpp"

namespace kitty
{
 
enum Unate_type { BINATE, POS_UNATE, NEG_UNATE };

template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>> 
bool tt_bitwise_less_equal( TT& lhs, TT& rhs )
{
	assert( lhs.num_vars() == rhs.num_vars() );
	
	for ( uint64_t i = 0; i < lhs.num_bits(); i++ )
	{
		if ( get_bit( lhs, i ) > get_bit( rhs, i ) ) return false;
	}
	return true;
}	


template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>> 
bool tt_bitwise_greater_equal( TT& lhs, TT& rhs )
{
	assert( lhs.num_vars() == rhs.num_vars() );
	
	for ( uint64_t i = 0; i < lhs.num_bits(); i++ )
	{
		if ( get_bit( lhs, i ) < get_bit( rhs, i ) ) return false;
	}
	return true;
}


template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>  
Unate_type is_unate_in_var( uint8_t var_num, TT& tt )
{
	TT cofactor_true  = cofactor1( tt, var_num );
	TT cofactor_false = cofactor0( tt, var_num );
		
	if( tt_bitwise_greater_equal( cofactor_true, cofactor_false ) ) 
    {
		return POS_UNATE;
	}
	else if ( tt_bitwise_greater_equal( cofactor_false, cofactor_true ) )
	{
		flip_inplace( tt, var_num );
		
		return NEG_UNATE;
	}
	else
	{
		return BINATE;
	}	
}	


template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_unate( TT& tt, std::vector<bool>& should_invert )
{
	for ( uint8_t i = 0; i < tt.num_vars(); i++)
	{
		Unate_type unateness = is_unate_in_var( i, tt);
		
		if ( unateness == POS_UNATE )
		{
			should_invert.at(i) = false; 
		}
		else if ( unateness == NEG_UNATE )
		{
			should_invert.at(i) = true;
		}
		else
		{
			return false;
		}
	}	

	return true;
}	  
  
  
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool ilp_solve( std::vector<int64_t>& linear_form, const TT& fstar )
{
	// Create lp context
	lprec *lp( make_lp( 0, 1+fstar.num_vars() ) );
		
	// Function to minimize
	std::vector<REAL> obj_fn_row( 2+fstar.num_vars(), 1.0 );
	set_obj_fn( lp, obj_fn_row.data() );
	set_minim(lp);
	
	// Remove prints from terminal
	set_verbose( lp, 0 );
	
	// All weights and T are positive
	std::vector<REAL> ilp_row( 2+fstar.num_vars(), 0.0 );
	
	for (uint32_t i = 0; i < fstar.num_vars()+1; i++)
	{
		std::fill( ilp_row.begin(), ilp_row.end(), 0.0 ); //reset vector
		ilp_row.at( 1+i ) = 1.0;
		add_constraint( lp, ilp_row.data(), GE, 0.0 );
	}
	
	// All variables are integers
	for( uint8_t i = 1; i < 2+fstar.num_vars(); i++ )
	{
		set_int(lp, i, TRUE);
	}
	
	// Define On-set constraints
	std::vector<cube> on_cubes = isop( fstar );
	
	for ( cube cub : on_cubes )
	{
		std::fill( ilp_row.begin(), ilp_row.end(), 0.0 ); //reset vector
		for (uint32_t i = 0; i < fstar.num_vars(); i++)
		{
			// If var is in cube and is not inverted
			if ( cub.get_bit( i ) && cub.get_mask( i ) )
			{
				ilp_row.at( 1+i ) = 1.0;
			}	
		}	
		ilp_row[ fstar.num_vars()+1 ] = -1.0;
		add_constraint( lp, ilp_row.data(), GE, 0.0 );
	}	
	
	// Define Off-set constraints
	std::vector<cube> off_cubes = isop( unary_not( fstar ) );
	std::fill( ilp_row.begin(), ilp_row.end(), 0.0 );

	for ( cube cub : off_cubes )
	{
		std::fill( ilp_row.begin(), ilp_row.end(), 0.0 ); //reset vector
		for (uint32_t i = 0; i < fstar.num_vars(); i++)
		{
			if ( !cub.get_mask(i) || ( cub.get_mask(i) && cub.get_bit(i) ) )
			{
				ilp_row.at( 1+i ) = 1.0;
			}	
		}
		ilp_row.at( fstar.num_vars()+1 ) = -1.0;
		add_constraint( lp, ilp_row.data(), LE, -1.0 );
	}	
	
	int ilp_status = solve(lp);
	std::vector<REAL> result( 1+fstar.num_vars() );

	get_variables( lp, result.data() );
	delete_lp(lp);
	
	linear_form.insert(linear_form.begin(), result.begin(), result.end());

	
	if ( ilp_status )
	{
		return false;
	}	
	
	return true;
}
  
  
/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;  
  std::vector<bool> should_invert( tt.num_vars(), false );

  TT tt_fstar = tt;

  // Check if function is unate and inverts negative unate variables if needed
  if ( !is_unate( tt_fstar, should_invert ) )
  {
	return false;
  }

  // Solves the ILP problem and checks if there is a solution
  if ( !ilp_solve( linear_form, tt_fstar ) ) return false;
  
  
  // Corrects the linear form vector associated with fstar to get the one associated with f
  for (uint64_t i = 0; i < tt_fstar.num_vars(); i++)
  {
	if ( should_invert.at(i) == true )
	{
		linear_form.at( tt_fstar.num_vars() ) = linear_form.at( tt_fstar.num_vars() ) - linear_form.at(i);
		linear_form.at(i) = -linear_form.at(i);
	}	
  }
  
  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  if ( plf )
  {
    *plf = linear_form;
  }

  return true;
}

} /* namespace kitty */
