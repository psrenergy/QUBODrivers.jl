# ~*~ :: QUBOTools :: ~*~ #

# Casting routes i.e. source => target pairs of senses and domains:
source_sense(sampler::AutomaticSampler) = QUBOTools.sense(sampler.model)
target_sense(sampler::AutomaticSampler) = sampler.sense

source_domain(sampler::AutomaticSampler) = QUBOTools.domain(sampler.model)
target_domain(sampler::AutomaticSampler) = sampler.domain

function QUBOTools.backend(sampler::AutomaticSampler)
    return QUBOTools.cast(
        source_sense(sampler) => target_sense(sampler),
        QUBOTools.cast(source_domain(sampler) => target_domain(sampler), sampler.model),
    )
end

# This is important to ensure aliasing:
function QUBOTools.metadata(sampler::AutomaticSampler)
    return QUBOTools.metadata(sampler.model)
end

function QUBOTools.start(sampler::AutomaticSampler)
    return QUBOTools.start(sampler.model)
end

# ~*~ :: MathOptInterface :: ~*~ #
function MOI.empty!(sampler::AutomaticSampler)
    sampler.model = nothing

    return sampler
end

function MOI.is_empty(sampler::AutomaticSampler)
    return isnothing(sampler.model)
end

function MOI.optimize!(sampler::AutomaticSampler)
    return _sample!(sampler)
end

function MOI.copy_to(sampler::AutomaticSampler{T}, model::MOI.ModelLike) where {T}
    MOI.empty!(sampler)

    sampler.model = parse_model(T, model)::QUBOTools.Model{VI,T}

    ws = QUBOTools.warm_start(sampler)::Dict{VI,Int}

    # Collect warm-start values
    for v in MOI.get(model, MOI.ListOfVariableIndices())
        x = MOI.get(model, MOI.VariablePrimalStart(), v)

        MOI.set(sampler, MOI.VariablePrimalStart(), v, x)

        if !isnothing(x)
            ws[v] = QUBOTools.cast(
                source_domain(sampler) => target_domain(sampler),
                round(Int, x),
            )
        end
    end

    return MOIU.identity_index_map(model)
end

function MOI.get(
    sampler::AutomaticSampler,
    st::Union{MOI.PrimalStatus,MOI.DualStatus},
    ::VI,
)
    if !(1 <= st.result_index <= MOI.get(sampler, MOI.ResultCount()))
        return MOI.NO_SOLUTION
    else
        # This status is also not very accurate, but all points are feasible
        # in a general sense since these problems are unconstrained.
        return MOI.FEASIBLE_POINT
    end
end

function MOI.get(sampler::AutomaticSampler, ::MOI.RawStatusString)
    solution_metadata = QUBOTools.metadata(QUBOTools.sampleset(sampler.model))

    if !haskey(solution_metadata, "status")
        return ""
    else
        return solution_metadata["status"]::String
    end
end

MOI.supports(::AutomaticSampler, ::MOI.RawStatusString) = true

function MOI.get(sampler::AutomaticSampler, ::MOI.ResultCount)
    return length(QUBOTools.sampleset(sampler.model))
end

function MOI.get(sampler::AutomaticSampler, ::MOI.TerminationStatus)
    ω = QUBOTools.sampleset(sampler.model)

    if isempty(ω)
        if isempty(QUBOTools.metadata(ω))
            return MOI.OPTIMIZE_NOT_CALLED
        else
            return MOI.OTHER_ERROR
        end
    else
        # This one is a little bit tricky...
        # It is nice if samplers implement this method in order to give
        # more accurate information.
        return MOI.LOCALLY_SOLVED
    end
end

function MOI.get(sampler::AutomaticSampler{T}, ::MOI.ObjectiveSense) where {T}
    sense = QUBOTools.sense(sampler.model)

    if sense === QUBOTools.Min
        return MOI.MIN_SENSE
    else
        return MOI.MAX_SENSE
    end
end

function MOI.get(sampler::AutomaticSampler, ov::MOI.ObjectiveValue)
    ω = QUBOTools.sampleset(sampler.model)
    i = ov.result_index
    n = length(ω)

    if isempty(ω)
        error("Invalid result index '$i'; There are no solutions")
    elseif !(1 <= i <= n)
        error("Invalid result index '$i'; There are $(n) solutions")
    end

    if MOI.get(sampler, MOI.ObjectiveSense()) === MOI.MAX_SENSE
        i = n - i + 1
    end

    return QUBOTools.value(ω, i)
end

function MOI.get(sampler::AutomaticSampler, ::MOI.SolveTimeSec)
    return QUBOTools.effective_time(QUBOTools.sampleset(sampler.model))
end

function MOI.get(sampler::AutomaticSampler{T}, vp::MOI.VariablePrimal, vi::VI) where {T}
    ω = QUBOTools.sampleset(sampler.model)
    n = length(ω)
    i = vp.result_index

    if isempty(ω)
        error("Invalid result index '$i'; There are no solutions")
    elseif !(1 <= i <= n)
        error("Invalid result index '$i'; There are $(n) solutions")
    end

    variable_map = QUBOTools.variable_map(sampler.model)

    if !haskey(variable_map, vi)
        error("Variable index '$vi' not in model")
    end

    if MOI.get(sampler, MOI.ObjectiveSense()) === MOI.MAX_SENSE
        i = n - i + 1
    end

    j = variable_map[vi]::Integer
    s = QUBOTools.state(ω, i, j)

    return convert(T, s)
end

function MOI.get(sampler::AutomaticSampler, ::MOI.NumberOfVariables)
    return QUBOTools.domain_size(sampler.model)
end

function QUBOTools.qubo(sampler::AutomaticSampler, type::Type = Dict)
    @assert !isnothing(sampler.model)

    n = QUBOTools.domain_size(sampler.model)

    L, Q, α, β = QUBOTools.cast(
        source_sense(sampler) => target_sense(sampler),
        # model terms and coefficients
        QUBOTools.linear_terms(sampler.model),
        QUBOTools.quadratic_terms(sampler.model),
        QUBOTools.scale(sampler.model),
        QUBOTools.offset(sampler.model),
    )

    L, Q, α, β =
        QUBOTools.cast(source_domain(sampler) => target_domain(sampler), L, Q, α, β)

    return QUBOTools.qubo(type, n, L, Q, α, β)
end

function QUBOTools.ising(sampler::AutomaticSampler, type::Type = Dict)
    @assert !isnothing(sampler.model)

    n = QUBOTools.domain_size(sampler.model)

    L, Q, α, β = QUBOTools.cast(
        source_sense(sampler) => target_sense(sampler),
        # model terms and coefficients
        QUBOTools.linear_terms(sampler.model),
        QUBOTools.quadratic_terms(sampler.model),
        QUBOTools.scale(sampler.model),
        QUBOTools.offset(sampler.model),
    )

    L, Q, α, β =
        QUBOTools.cast(source_domain(sampler) => target_domain(sampler), L, Q, α, β)

    return QUBOTools.ising(type, n, L, Q, α, β)
end

# ~*~ File IO: Base API ~*~ #
# function Base.write(
#     filename::AbstractString,
#     sampler::AutomaticSampler,
#     fmt::QUBOTools.AbstractFormat = QUBOTools.infer_format(filename),
# )
#     return QUBOTools.write_model(filename, sampler.model, fmt)
# end

# function Base.read!(
#     filename::AbstractString,
#     sampler::AutomaticSampler,
#     fmt::QUBOTools.AbstractFormat = QUBOTools.infer_format(filename),
# )
#     sampler.source = QUBOTools.read_model(filename, fmt)
#     sampler.target = QUBOTools.format(sampler, sampler.source)

#     return sampler
# end

function warm_start(sampler::AutomaticSampler, i::Integer)
    v = QUBOTools.variable_inv(sampler, i)
    x = MOI.get(sampler, MOI.VariablePrimalStart(), v)

    if isnothing(x)
        return nothing
    else
        return QUBOTools.cast(
            source_domain(sampler) => target_domain(sampler),
            round(Int, x),
        )
    end
end

function warm_start(sampler::AutomaticSampler{T}) where {T}
    n = MOI.get(sampler, MOI.NumberOfVariables())
    s = sizehint!(Dict{Int,Int}(), n)

    for i = 1:n
        x = warm_start(sampler, i)
        isnothing(x) || (s[i] = x)
    end

    return s
end