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

void print_vector(std::vector<REAL> vec)
{
	for (uint8_t i = 0; i < vec.size(); i++) 
	{
		std::cout << vec.at(i) << " "; 
	}
	std::cout << std::endl;
}	

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
	
	std::cout << "Check wether is unate in var " << int(var_num) << std::endl;
	
	std::cout << "Cofactor true:" << std::endl;
	print_binary( cofactor_true, std::cout);
	std::cout <<  std::endl;
	std::cout << "Cofactor false:" << std::endl;
	print_binary( cofactor_false, std::cout);
	std::cout <<  std::endl;
	
	
	if( tt_bitwise_greater_equal( cofactor_true, cofactor_false ) ) 
    {
		std::cout << "-> is positive unate in Var "<< var_num << var_num << std::endl;
		return POS_UNATE;
	}
	else if ( tt_bitwise_greater_equal( cofactor_false, cofactor_true ) )
	{
		std::cout << "-> is negative unate in Var "<< var_num << var_num << std::endl;
		flip_inplace( tt, var_num );
		std::cout << "The TT after fliping is: ";
		print_binary( tt, std::cout);
		std::cout <<  std::endl;
		
		return NEG_UNATE;
	}
	else
	{
		std::cout << "-> is binate in Var "<< var_num << var_num << std::endl;
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
			should_invert[i] = false; 
		}
		else if ( unateness == NEG_UNATE )
		{
			should_invert[i] = true;
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
	
	
	std::cout << "Number of Columns = " << get_Ncolumns( lp ) << std::endl;
	
	// Function to minimize
	std::vector<REAL> obj_fn_row( 2+fstar.num_vars(), 1.0 );
	
	std::cout << "Set ojective fun" << std::endl;
	print_vector(obj_fn_row);
	
	set_obj_fn( lp, obj_fn_row.data() );
	set_minim(lp);
	
	// All weights and T are positive
	std::vector<REAL> ilp_row( 2+fstar.num_vars(), 0.0 );
	
	std::cout << "Contraint all positive" << std::endl;
	
	for (uint32_t i = 0; i < fstar.num_vars()+1; i++)
	{
		std::fill( ilp_row.begin(), ilp_row.end(), 0.0 );
		ilp_row.at(i+1) = 1.0;
		print_vector(ilp_row);
		add_constraint( lp, ilp_row.data(), GE, 0.0 );
	}
	
	// All variables are integers
	for( uint8_t i = 1; i < 2+fstar.num_vars(); i++ )
	{
		set_int(lp, i, TRUE);
	}
	
	// Define On-set constraints
	std::vector<cube> on_cubes = isop( fstar );
	
	std::cout << "On-set Cubes and constraints" << std::endl;
	print_cubes(on_cubes);
	
	
	for ( cube cub : on_cubes )
	{
		std::fill( ilp_row.begin(), ilp_row.end(), 0.0 );
		for (uint32_t i = 0; i < fstar.num_vars(); i++)
		{
			if ( cub.get_bit(i) && cub.get_mask(i) )
			{
				ilp_row[i+1] = 1.0;
			}	
		}	
		ilp_row[ fstar.num_vars()+1 ] = -1.0;
		print_vector(ilp_row);
		add_constraint( lp, ilp_row.data(), GE, 0.0 );
	}	
	
	// Define Off-set constraints
	std::vector<cube> off_cubes = isop( unary_not( fstar ) );
	std::fill( ilp_row.begin(), ilp_row.end(), 0.0 );
	
	std::cout << "Off-set Cubes and constraints" << std::endl;
	print_cubes(off_cubes);
	
	for ( cube cub : off_cubes )
	{
		std::fill( ilp_row.begin(), ilp_row.end(), 0.0 );
		for (uint32_t i = 0; i < fstar.num_vars(); i++)
		{
			if ( !cub.get_mask(i) || ( cub.get_mask(i) && cub.get_bit(i) ) )
			{
				ilp_row[i+1] = 1.0;
			}	
		}
		ilp_row[ fstar.num_vars()+1 ] = -1.0;
		print_vector(ilp_row);
		add_constraint( lp, ilp_row.data(), LE, -1.0 );
	}	
	
	int ilp_status = solve(lp);
	std::vector<REAL> result( 1+fstar.num_vars() );
	
	std::cout << "Result vector" << std::endl;
	
	get_variables( lp, result.data() );
	print_vector(result);
	
	
	std::cout << "Solving status  " << ilp_status << std::endl;
	/*
	for (uint32_t i = 0; i < 1+fstar.num_vars(); i++)
	{
		linear_form.at(i) = int64_t(result.at(i));
	}
	*/
	linear_form.insert(linear_form.begin(), result.begin(), result.end());
	std::cout << "End of ILP solving" << std::endl;
	delete_lp(lp);
	
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


  std::cout << " *********  Check if threshold function  ************" << std::endl;
  std::cout << "The TT is: ";
  print_binary( tt, std::cout);
  std::cout << std::endl;
  
  std::vector<bool> should_invert( tt.num_vars(), false );

  TT tt_fstar = tt;

  if ( !is_unate( tt_fstar, should_invert ) )
  {
	std::cout << "The function is not unate" << std::endl;
	return false;
  }
  
  std::cout << "Should invert vector" << std::endl;
  for ( uint8_t i = 0; i < should_invert.size(); i++ )
  {
    std::cout <<  should_invert.at(i) << " ";
  }  
  std::cout << std::endl;
  
  if ( !ilp_solve( linear_form, tt_fstar ) ) return false;
  
  
  std::cout << "Content of linear form before variable recovery:" << std::endl;
  for (uint8_t i = 0 ; i < linear_form.size(); i++ )
  {
     std::cout << linear_form.at(i) << " ";
  }	  
  std::cout << std::endl;
  
  std::cout << "Let's start variable recovery" << std::endl;
  
  for (uint64_t i = 0; i < tt_fstar.num_vars(); i++)
  {
	std::cout << "In the for loop" << std::endl;
	if ( should_invert.at(i) == true )
	{
		std::cout << "Substract weight" << std::endl;
		linear_form.at( tt_fstar.num_vars() ) = linear_form.at( tt_fstar.num_vars() ) - linear_form.at(i);
		std::cout << "Change sign" << std::endl;
		linear_form.at(i) = -linear_form.at(i);
		std::cout << "end of correction "<< i << std::endl;
	}	
  }
  
  
  std::cout << "let's assign the pointer" << std::endl;
  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  if ( plf )
  {
    *plf = linear_form;
  }
  
  std::cout << "End of is threshold function" << std::endl;
  return true;
}

} /* namespace kitty */
