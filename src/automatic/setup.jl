const __MODULES = Set{Module}()

function __setup_error(msg::String)
    error("Invalid usage of @setup: $msg")
end

function __setup_parse_id(id::Symbol)
    if Base.isidentifier(id)
        return id
    else
        __setup_error("Invalid identifier for sampler: '$id'")
    end
end

function __setup_parse_id()
    return :Optimizer
end

function __setup_parse_param(::Val{X}, ::Any) where {X}
    __setup_error(
        "Invalid parameter '$X', valid options are: 'name', 'version', 'domain', 'attributes'",
    )
end

function __setup_parse_param(::Val{:name}, value)
    if value isa String
        return value
    else
        __setup_error("Parameter 'name' must be a 'String'")
    end
end

function __setup_parse_param(::Val{:version}, value)
    if value isa VersionNumber
        return value
    else
        __setup_error("Parameter 'version' must be a 'VersionNumber'")
    end
end

function __setup_parse_param(::Val{:sense}, _value)
    value = if _value isa QuoteNode
        _value.value
    elseif value isa String
        Symbol(_value)
    else
        _value
    end

    if (value === :min || value === :max)
        return value
    else
        __setup_error("parameter 'sense' must be either ':min' or ':max', not '$_value'")
    end
end

function __setup_parse_param(::Val{:domain}, _value)
    value = if _value isa QuoteNode
        _value.value
    elseif _value isa String
        Symbol(_value)
    else
        _value
    end

    if (value === :bool || value === :spin)
        return value
    else
        __setup_error("parameter 'domain' must be either ':bool' or ':spin', not '$_value'")
    end
end

function __setup_parse_param(::Val{:attributes}, value)
    if value isa Expr && value.head === :block
        return Dict{Symbol,Any}[
            attr for attr in __setup_parse_attr.(value.args) if !isnothing(attr)
        ]
    else
        __setup_error("Parameter 'attributes' must be a `begin ... end` block")
    end
end

function __setup_parse_attr(stmt)
    if stmt isa LineNumberNode
        return nothing
    elseif !(stmt isa Expr && stmt.head === :(=))
        __setup_error(
            "Each attribute definition must be an assignment to a default value ($stmt)",
        )
    end

    attr, default = stmt.args

    type    = nothing
    optattr = nothing
    rawattr = nothing

    if attr isa Symbol # ~ MOI attribute only
        if !(Base.isidentifier(attr))
            __setup_error("attribute identifier '$attr' is not a valid one")
        end

        optattr = attr
    elseif attr isa String # ~ Raw attribute only
        rawattr = attr
    elseif attr isa Expr && attr.head === :(::)
        attr, type = attr.args

        if attr isa Symbol
            if !(Base.isidentifier(attr))
                __setup_error("attribute identifier '$attr' is not a valid one")
            end

            optattr = attr
        elseif attr isa String
            rawattr = attr
        elseif attr isa Expr && (attr.head === :ref || attr.head === :call)
            optattr, rawattr = attr.args

            if optattr isa Symbol && rawattr isa String
                if !(Base.isidentifier(optattr))
                    __setup_error("attribute identifier '$optattr' is not a valid one")
                end
            else
                __setup_error("invalid attribute identifier '$name($raw)'")
            end
        else
            __setup_error("invalid attribute identifier '$attr'")
        end
    elseif attr isa Expr && (attr.head === :ref || attr.head === :call)
        optattr, rawattr = attr.args

        if optattr isa Symbol && rawattr isa String
            if !(Base.isidentifier(optattr))
                __setup_error("attribute identifier '$optattr' is not a valid one")
            end
        else
            __setup_error("invalid attribute identifier '$name[$rawattr]'")
        end
    else
        __setup_error("invalid attribute signature '$attr'")
    end

    return Dict{Symbol,Any}(
        :type    => type,
        :default => default,
        :optattr => optattr,
        :rawattr => rawattr,
    )
end

function __setup_parse_params(block::Expr)
    if !(block.head === :block)
        __setup_error("Sampler configuration must be provided within a `begin ... end` block")
    end

    params = Dict{Symbol,Any}(
        :name       => "",
        :sense      => :min,
        :domain     => :bool,
        :version    => v"1.0.0",
        :attributes => Dict{Symbol,Any}[],
    )

    for item in block.args
        if item isa LineNumberNode
            continue
        elseif item isa Expr && item.head === :(=)
            param, value = item.args

            if param isa Symbol && Base.isidentifier(param)
                params[param] = __setup_parse_param(Val(param), value)
            else
                __setup_error("sampler parameter key must be a valid identifier")
            end
        else
            __setup_error("sampler parameters must be `key = value` pairs")
        end
    end

    # Post-processing
    params[:sense]      = QUBOTools.sense(params[:sense])
    params[:domain]     = QUBOTools.domain(params[:domain])
    params[:attributes] = __setup_attr.(params[:attributes])

    return params
end

function __setup_parse_params()
    __DEFAULT_PARAMETERS()
end

function __setup_parse(args...)
    __setup_error("macro takes exactly one or two arguments")
end

function __setup_parse(expr)
    if expr isa Symbol # Name
        return (__setup_parse_id(expr), __setup_parse_params())
    elseif (expr isa Expr && expr.head === :block)
        return (__setup_parse_id(), __setup_parse_params(expr))
    else
        __setup_error(
            "Single argument must be either an identifier or a `begin ... end` block",
        )
    end
end

function __setup_parse()
    return (__setup_parse_id(), __setup_parse_params())
end

function __setup_parse(id, block)
    params = Dict{Symbol,Any}()

    if !(id isa Symbol)
        __setup_error("First argument must be an identifier")
    end

    params[:id] = __setup_parse_id(id)

    if !(block isa Expr && block.head === :block)
        __setup_error("Second argument must be a `begin ... end` block")
    end

    merge!(params, __setup_parse_params(block))

    return params
end

function __setup_attr(attr)
    type    = attr[:type]
    default = attr[:default]
    optattr = attr[:optattr]
    rawattr = attr[:rawattr]

    if !isnothing(optattr) && !isnothing(rawattr)
        return quote
            struct $(esc(optattr)) <: QUBODrivers.AbstractSamplerAttribute end

            push!(
                __ATTRIBUTES,
                QUBODrivers.AttributeWrapper{$(esc(optattr)),$(esc(type))}(
                    $(esc(default));
                    rawattr = $(esc(rawattr)),
                    optattr = $(esc(optattr))(),
                ),
            )
        end
    elseif !isnothing(optattr)
        return quote
            struct $(esc(optattr)) <: QUBODrivers.AbstractSamplerAttribute end

            push!(
                __ATTRIBUTES,
                QUBODrivers.AttributeWrapper{$(esc(optattr)),$(esc(type))}(
                    $(esc(default));
                    optattr = $(esc(optattr))(),
                ),
            )
        end
    elseif !isnothing(rawattr)
        return quote
            push!(
                __ATTRIBUTES,
                QUBODrivers.AttributeWrapper{Nothing,$(esc(type))}(
                    $(esc(default));
                    rawattr = $(esc(rawattr)),
                ),
            )
        end
    else
        error("Looks like some assertions were skipped. Did you turn any optimizations on?")
    end
end

@doc raw"""
    @setup(expr)

The `@setup` macro receives a `begin ... end` block with an attribute definition on each of the block's statements.

All attributes must be presented as an assignment to the default value of that attribute. To create a MathOptInterface optimizer attribute, an identifier must be present on the left hand side. If a solver-specific, raw attribute is desired, its name must be given as a string, e.g. between double quotes. In the special case where an attribute could be accessed in both ways, the identifier must be followed by the parenthesised raw attribute string. In any case, the attribute type can be specified typing the type assertion operator `::` followed by the type itself just before the equal sign.

For example, a list of the valid syntax variations for the *number of reads* attribute follows:
    - `"num_reads" = 1_000`
    - `"num_reads"::Integer = 1_000`
    - `NumberOfReads = 1_000`
    - `NumberOfReads::Integer = 1_000`
    - `NumberOfReads["num_reads"] = 1_000`
    - `NumberOfReads["num_reads"]::Integer = 1_000`

## Example

```
QUBODrivers.@setup Optimizer begin
    name    = "Super Sampler"
    sense   = :max
    domain  = :spin
    version = v"1.0.2"
    attributes = begin
        NumberOfReads["num_reads"]::Integer = 1_000
        SuperAttribute["super_attr"] = nothing
    end
end
```
"""
macro setup(raw_args...)
    # Check context
    if __module__ === Main
        __setup_error("macro must be called from within a module (not Main)")
    elseif __module__ ∈ QUBODrivers.__MODULES
        __setup_error("macro should be called only once within a module")
    else
        push!(QUBODrivers.__MODULES, __module__)
    end

    # Parse parameters
    args   = map(a -> macroexpand(__module__, a), raw_args)
    params = __setup_parse(args...)

    # Collect parameters
    _id         = params[:id]
    _name       = params[:name]
    _sense      = params[:sense]
    _domain     = params[:domain]
    _version    = params[:version]
    _attributes = params[:attributes]

    # For this mechanism to work it is very important that the
    # @setup macro is called at most once inside each module.
    return quote
        mutable struct $(esc(_id)){T} <: QUBODrivers.AutomaticSampler{T}
            # Sense & Domain
            sense::QUBOTools.Sense
            domain::QUBOTools.Domain
            # QUBOTools model
            model::Union{QUBOTools.Model{VI,T,Int},Nothing}
            # Attributes
            attr_data::QUBODrivers.AttributeData{T}
        end
        
        const __ATTRIBUTES = QUBODrivers.AttributeWrapper[]

        function $(esc(_id)){T}(args...; kws...) where {T}
            return $(esc(_id)){T}(
                $(esc(_sense)),                             # sense
                $(esc(_domain)),                            # domain
                nothing,                                    # model
                QUBODrivers.AttributeData{T}(__ATTRIBUTES), # attr_data
            )
        end

        $(esc(_id))(args...; kws...) = $(esc(_id)){Float64}(args...; kws...)

        $(_attributes...)

        # MOI interface
        MOI.get(::$(esc(_id)), ::MOI.SolverName)    = $(esc(_name))
        MOI.get(::$(esc(_id)), ::MOI.SolverVersion) = $(esc(_version))
    end
end